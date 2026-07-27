(** Scheduler differential (C5, adr-0019): the OCaml [Rkv.Sched] realizer vs the
    extracted reference [Sched.run_sched].

    Same fibers, same INJECTED schedule → same observable, on both sides.  The native
    side runs real OCaml fiber thunks (mirroring the reference [tm] fibers fA/fB/
    fProd/fCons/fD1/fD2/fSp/bodies_sp of theories/Sched.v) under [Rkv.Sched.run] with a
    [Rkv.Trace] handler wrapped around it (Trace propagates out of the scheduler exactly
    as OTrace propagates through the shared world); the reference side runs the extracted
    [run_sched] on the SAME proven sample states (Sched.s_int/s_pc/s_dead/s_sp).  Compared:
    the chronological trace, the completed-fiber outcomes, and the deadlock verdict
    ([sresult_of]).

    Schedules include the proven instances (interleaving_121, producer_consumer,
    deadlock, spawn_runs) AND adversarial ones per adr-0019: starvation (one fiber never
    scheduled), immediate-block (recv-first on an empty channel), ping-pong, and a short
    schedule that leaves fibers live (deadlock as a VALUE, never a hang). *)

module E = Ref_extracted.EffIR
module Sc = Ref_extracted.Sched
module D = Ref_extracted.Datatypes
module R = Rkv.Rval

(* ---- conversions ------------------------------------------------------------ *)

let coq_sched (l : int list) =
  Coqconv.coq_list_of (List.map (fun i -> Coqconv.coqz_of_z (Z.of_int i)) l)

let outcome_to_rval = function E.ORet d -> Coqconv.rval_of_dval d | E.OErr d -> Coqconv.rval_of_dval d
let pair_to_id_out = function
  | D.Coq_pair (z, o) -> (Coqconv.z_of_coqz z, outcome_to_rval o)

(* reference-side observable: (chronological trace, done outcomes, verdict) *)
type verdict = VDone of (Z.t * R.t) list | VStuck of Z.t list * (Z.t * R.t) list

let ref_run bodies (sched : int list) (s0 : Sc.sst) : R.t list * verdict =
  let s = Sc.run_sched bodies (coq_sched sched) s0 in
  let trace =
    List.rev_map Coqconv.rval_of_dval (Coqconv.list_of_coq (Sc.swld s).E.trace)
  in
  let verdict =
    match Sc.sresult_of s with
    | Sc.Completed d -> VDone (List.map pair_to_id_out (Coqconv.list_of_coq d))
    | Sc.Stuck (ids, d) ->
        VStuck
          ( List.map Coqconv.z_of_coqz (Coqconv.list_of_coq ids),
            List.map pair_to_id_out (Coqconv.list_of_coq d) )
  in
  (trace, verdict)

(* ---- native fibers (mirror theories/Sched.v exactly) ------------------------ *)

let ri i = R.Int (Z.of_int i)
let nb_native : Z.t -> unit -> R.t = fun _ () -> R.Unit
let bodies_sp_native : Z.t -> unit -> R.t =
  fun i () -> if Z.equal i Z.zero then (Rkv.Trace.emit (ri 99); R.Unit) else R.Unit

let f_a () = Rkv.Trace.emit (ri 10); ignore (Rkv.Sched.yield ()); Rkv.Trace.emit (ri 11); R.Unit
let f_b () = Rkv.Trace.emit (ri 20); R.Unit
let f_prod () = ignore (Rkv.Sched.chan_send Z.zero (ri 42)); R.Unit
let f_cons () = let v = Rkv.Sched.chan_recv Z.zero in Rkv.Trace.emit v; R.Unit
let f_d1 () = Rkv.Sched.chan_recv Z.zero
let f_d2 () = Rkv.Sched.chan_recv Z.one
let f_sp () = Rkv.Sched.spawn Z.zero

let native_run ?(chans = []) ?(next_fib = Z.of_int 3) ?(next_chan = Z.one)
    (bodies : Z.t -> unit -> R.t) (sched : int list)
    (init : (Z.t * (unit -> R.t)) list) : R.t list * verdict =
  let buf = ref [] in
  let res =
    Rkv.Trace.run buf (fun () ->
        Rkv.Sched.run ~next_fib ~next_chan ~chans ~bodies
          ~schedule:(List.map Z.of_int sched) init)
  in
  let verdict =
    match res with
    | Rkv.Sched.Completed d -> VDone d
    | Rkv.Sched.Stuck (ids, d) -> VStuck (ids, d)
  in
  (Rkv.Trace.contents buf, verdict)

(* ---- equality / reporting --------------------------------------------------- *)

let trace_eq a b = List.length a = List.length b && List.for_all2 R.equal a b
let dl_eq a b =
  List.length a = List.length b
  && List.for_all2 (fun (i, v) (j, w) -> Z.equal i j && R.equal v w) a b
let ids_eq a b = List.length a = List.length b && List.for_all2 Z.equal a b
let verdict_eq a b =
  match (a, b) with
  | VDone d1, VDone d2 -> dl_eq d1 d2
  | VStuck (i1, d1), VStuck (i2, d2) -> ids_eq i1 i2 && dl_eq d1 d2
  | _ -> false

let show_tr l = "[" ^ String.concat "; " (List.map R.to_string l) ^ "]"
let show_v = function
  | VDone d -> "Done[" ^ String.concat ";" (List.map (fun (i, v) -> Z.to_string i ^ "->" ^ R.to_string v) d) ^ "]"
  | VStuck (i, d) ->
      "Stuck(live=[" ^ String.concat ";" (List.map Z.to_string i) ^ "],done=["
      ^ String.concat ";" (List.map (fun (i, v) -> Z.to_string i ^ "->" ^ R.to_string v) d) ^ "])"

let fails = ref 0
let count = ref 0

(* one case: [name] runs the SAME (bodies, schedule, init) on both sides *)
let check name ~bodies_ref ~bodies_nat ~sched ~s0 ~chans ~next_fib ~next_chan ~init =
  incr count;
  let rt, rv = ref_run bodies_ref sched s0 in
  let nt, nv = native_run ~chans ~next_fib ~next_chan bodies_nat sched init in
  if not (trace_eq rt nt && verdict_eq rv nv) then begin
    incr fails;
    Printf.printf "MISMATCH %s\n  ref  trace=%s verdict=%s\n  nat  trace=%s verdict=%s\n"
      name (show_tr rt) (show_v rv) (show_tr nt) (show_v nv)
  end

(* ---- the cases -------------------------------------------------------------- *)

let int_init = [ (Z.one, f_a); (Z.of_int 2, f_b) ]
let pc_init = [ (Z.one, f_prod); (Z.of_int 2, f_cons) ]
let dead_init = [ (Z.one, f_d1); (Z.of_int 2, f_d2) ]
let sp_init = [ (Z.one, f_sp) ]

let () =
  (* interleaving (s_int): nb bodies, no chans, nf=3 nc=1 *)
  List.iter
    (fun sched ->
      check (Printf.sprintf "interleave %s" (String.concat "," (List.map string_of_int sched)))
        ~bodies_ref:Sc.nb ~bodies_nat:nb_native ~sched ~s0:Sc.s_int
        ~chans:[] ~next_fib:(Z.of_int 3) ~next_chan:Z.one ~init:int_init)
    [ [1;2;1]; [1;1;2]; [2;1;1]; [1;2;1;2]; [2;2;1;1]; [1;2]; [1;1;1;1] ];

  (* producer/consumer (s_pc): chan 0 pre-made, nf=3 nc=1 *)
  List.iter
    (fun sched ->
      check (Printf.sprintf "prodcons %s" (String.concat "," (List.map string_of_int sched)))
        ~bodies_ref:Sc.nb ~bodies_nat:nb_native ~sched ~s0:Sc.s_pc
        ~chans:[ Z.zero ] ~next_fib:(Z.of_int 3) ~next_chan:Z.one ~init:pc_init)
    [ [1;2;2;1]; [2;1;2;2;1]; [2;2;1;2;1]; [1;2]; [2;2] ];

  (* deadlock (s_dead): chans 0,1 pre-made, nf=3 nc=2 *)
  List.iter
    (fun sched ->
      check (Printf.sprintf "deadlock %s" (String.concat "," (List.map string_of_int sched)))
        ~bodies_ref:Sc.nb ~bodies_nat:nb_native ~sched ~s0:Sc.s_dead
        ~chans:[ Z.zero; Z.one ] ~next_fib:(Z.of_int 3) ~next_chan:(Z.of_int 2) ~init:dead_init)
    [ [1;2;1;2]; [1;2]; [1;1]; [2;2;2] ];

  (* spawn (s_sp): bodies_sp, nf=2 nc=1 *)
  List.iter
    (fun sched ->
      check (Printf.sprintf "spawn %s" (String.concat "," (List.map string_of_int sched)))
        ~bodies_ref:Sc.bodies_sp ~bodies_nat:bodies_sp_native ~sched ~s0:Sc.s_sp
        ~chans:[] ~next_fib:(Z.of_int 2) ~next_chan:Z.one ~init:sp_init)
    [ [1;2;1]; [1;1]; [1]; [1;2] ];

  Printf.printf "SCHED DIFFERENTIAL: %d cases, %d fails\n" !count !fails;
  if !fails = 0 then
    print_endline "SCHED DIFFERENTIAL OK: native realizer == extracted run_sched (trace + outcomes + deadlock verdict)"
  else exit 1
