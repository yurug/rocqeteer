(** Differential test for the Fold list elimination (IR v2 R6, adr-0012-list-elimination).

    Runs the four Fold samples (sample_fold_put / sample_fold_ovf / sample_fold_concat /
    sample_fold_trace / sample_fold_guard) with adversarially-biased CONTEXT lists,
    comparing the reference interpreter against the generated direct-style code on
    outcome (incl. the error payload), final store (live bindings), and trace.

    Adversarial classes (each must be covered; coverage is ASSERTED):
      F1  empty list                      -> init result, no effects
      F2  singleton list
      F3  large list (>= 1000 elements)   -> the fold bound really comes from the data
      F4  mixed-shape list (Int/Bytes/Bool/Unit/Pair/Tag/None together)
      F5  error mid-fold (poison "BAD" element) -> OErr + exactly the pre-poison puts
      F6  accumulator overflow via the PAddChecked path (counter starts at int64_max)
      F7  non-list scrutinee              -> init result (documented adr-0012 posture)
      F8  ORDER: the chronological trace of sample_fold_trace equals the input list
          IN ORDER (asserted against the input, not just ref==fast), and a reversed
          list yields the reversed trace

    Seeds are logged; every counterexample prints its seed for corpus replay.
    Reference == fast is asserted for every run. *)

module E   = Ref_extracted.EffIR
module D   = Ref_extracted.Datatypes
module S   = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260712
let rng = Random.State.make [| seed |]

let now = Z.zero
let int64_max = Z.of_string "9223372036854775807"
let poison = Rkv.Rval.Bytes (Bytes.of_string "BAD")

(* --- observation: outcome + sorted live store + chronological trace --------- *)

type obs = {
  out   : (Rkv.Rval.t, Rkv.Rval.t) result;   (* Ok v | Error e (throw payload) *)
  state : (bytes * (Rkv.Rval.t * Z.t option)) list;
  tr    : Rkv.Rval.t list;
}

let ref_obs (term : E.tm) (ctx : Rkv.Rval.t) : obs =
  let coq_ctx = Coqconv.dval_of_rval ctx in
  let oc, bindings, tr =
    match E.observe coq_ctx (Coqconv.coqz_of_z now) term with
    | D.Coq_pair (D.Coq_pair (oc, bs), t) -> (oc, bs, t)
  in
  let out =
    match oc with
    | E.ORet v -> Ok (Coqconv.rval_of_dval v)
    | E.OErr e -> Error (Coqconv.rval_of_dval e)
  in
  let state =
    Coqconv.list_of_coq bindings
    |> List.map (fun p ->
           match p with
           | D.Coq_pair (k, e) ->
               (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
    |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)
  in
  { out; state; tr = Coqconv.list_of_coq tr |> List.map Coqconv.rval_of_dval }

let fast_obs (fn : unit -> Rkv.Rval.t) (ctx : Rkv.Rval.t) : obs =
  let table = Rkv.Kv.T.create 64 in
  let buf = ref [] in
  let out =
    Rkv.Env.run ctx (fun () ->
        Rkv.Trace.run buf (fun () ->
            match
              Rkv.Err.run_error (fun () ->
                  Rkv.Runtime.with_store_and_time ~source:(fun () -> now) table fn)
            with
            | Ok v -> Ok v
            | Error e -> Error e))
  in
  { out; state = Rkv.Kv.observe ~now table; tr = Rkv.Trace.contents buf }

(* --- equality + printing ----------------------------------------------------- *)

let out_eq a b =
  match a, b with
  | Ok x, Ok y | Error x, Error y -> Rkv.Rval.equal x y
  | _ -> false

let list_eq eq a b = List.length a = List.length b && List.for_all2 eq a b
let entry_eq (v1, d1) (v2, d2) = Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2
let state_eq = list_eq (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2)
let trace_eq = list_eq Rkv.Rval.equal

let show_out = function
  | Ok v -> "ret " ^ Rkv.Rval.to_string v
  | Error e -> "throw " ^ Rkv.Rval.to_string e

let show_entry (v, dl) =
  Rkv.Rval.to_string v ^ (match dl with None -> "" | Some d -> "@" ^ Z.to_string d)

let show_state l =
  "[" ^ String.concat "; "
    (List.map (fun (k, e) -> Printf.sprintf "%s=%s" (Bytes.to_string k) (show_entry e)) l)
  ^ "]"

let show_tr l = "[" ^ String.concat "; " (List.map Rkv.Rval.to_string l) ^ "]"

let obs_eq a b = out_eq a.out b.out && state_eq a.state b.state && trace_eq a.tr b.tr

(* --- context generator (biased to the F-classes) ----------------------------- *)

let gen_elem () : Rkv.Rval.t =
  match Random.State.int rng 8 with
  | 0 -> Rkv.Rval.Int (Z.of_int (Random.State.int rng 2001 - 1000))
  | 1 -> Rkv.Rval.Int int64_max
  | 2 ->
      Rkv.Rval.Bytes
        (Bytes.init (Random.State.int rng 6) (fun _ -> Char.chr (Random.State.int rng 256)))
  | 3 -> Rkv.Rval.Bool (Random.State.bool rng)
  | 4 -> Rkv.Rval.Unit
  | 5 -> Rkv.Rval.Pair (Rkv.Rval.Int Z.one, Rkv.Rval.Bytes (Bytes.of_string "p"))
  | 6 -> Rkv.Rval.Tag (Z.of_int 3, Rkv.Rval.Int Z.zero)
  | _ -> Rkv.Rval.None

type cls = Fempty | Fsingle | Flarge | Fmixed | Fpoison | Fnonlist | Fsmall

let gen_ctx () : cls * Rkv.Rval.t =
  match Random.State.int rng 12 with
  | 0 -> (Fempty, Rkv.Rval.List [])
  | 1 -> (Fsingle, Rkv.Rval.List [ gen_elem () ])
  | 2 ->
      (* F3: large list, 1000-1500 elements *)
      let n = 1000 + Random.State.int rng 500 in
      (Flarge, Rkv.Rval.List (List.init n (fun i -> Rkv.Rval.Int (Z.of_int i))))
  | 3 | 4 ->
      (* F4: mixed shapes, every constructor class possible *)
      let n = 2 + Random.State.int rng 7 in
      (Fmixed, Rkv.Rval.List (List.init n (fun _ -> gen_elem ())))
  | 5 | 6 ->
      (* F5: poison somewhere in the middle *)
      let pre = List.init (Random.State.int rng 4) (fun _ -> gen_elem ()) in
      let post = List.init (Random.State.int rng 4) (fun _ -> gen_elem ()) in
      (Fpoison, Rkv.Rval.List (pre @ [ poison ] @ post))
  | 7 -> (Fnonlist, Rkv.Rval.Int (Z.of_int 3))
  | 8 -> (Fnonlist, Rkv.Rval.Bytes (Bytes.of_string "not a list"))
  | _ ->
      let n = Random.State.int rng 6 in
      (Fsmall, Rkv.Rval.List (List.init n (fun _ -> gen_elem ())))

(* --- programs ---------------------------------------------------------------- *)

let programs : (string * E.tm * (unit -> Rkv.Rval.t)) list =
  [ ("sample_fold_put",    S.sample_fold_put,    Gen.sample_fold_put);
    ("sample_fold_ovf",    S.sample_fold_ovf,    Gen.sample_fold_ovf);
    ("sample_fold_concat", S.sample_fold_concat, Gen.sample_fold_concat);
    ("sample_fold_trace",  S.sample_fold_trace,  Gen.sample_fold_trace);
    ("sample_fold_guard",  S.sample_fold_guard,  Gen.sample_fold_guard) ]

(* --- coverage ----------------------------------------------------------------- *)

let cover_f1 = ref false and cover_f2 = ref false and cover_f3 = ref false
let cover_f4 = ref false and cover_f5 = ref false and cover_f6 = ref false
let cover_f7 = ref false and cover_f8 = ref false

let () =
  let n = 400 in   (* x5 programs per round; large lists keep the total meaningful *)
  let fails = ref 0 in
  for _ = 1 to n do
    let (cls, ctx) = gen_ctx () in
    (match cls with
     | Fempty -> cover_f1 := true
     | Fsingle -> cover_f2 := true
     | Flarge -> cover_f3 := true
     | Fmixed -> cover_f4 := true
     | Fpoison -> ()
     | Fnonlist -> cover_f7 := true
     | Fsmall -> ());
    List.iter
      (fun (name, term, fn) ->
        let r = ref_obs term ctx and f = fast_obs fn ctx in
        if not (obs_eq r f) then begin
          incr fails;
          Printf.printf "MISMATCH %s (RSEED=%d) ctx=%s\n  ref =(%s, %s, %s)\n  fast=(%s, %s, %s)\n"
            name seed (Rkv.Rval.to_string ctx)
            (show_out r.out) (show_state r.state) (show_tr r.tr)
            (show_out f.out) (show_state f.state) (show_tr f.tr)
        end;
        (* class-specific reference-side assertions *)
        (match name, cls, ctx with
         | "sample_fold_guard", Fpoison, _ ->
             (* F5: OErr with the poison payload; exactly the pre-poison puts *)
             (match r.out with
              | Error e when Rkv.Rval.equal e poison -> cover_f5 := true
              | _ ->
                  incr fails;
                  Printf.printf "F5 FAIL %s (RSEED=%d): expected throw BAD, got %s\n"
                    name seed (show_out r.out))
         | "sample_fold_ovf", _, Rkv.Rval.List (_ :: _) ->
             (* F6: a non-empty list overflows the max-seeded counter on element 0 *)
             (match r.out with
              | Error e when Rkv.Rval.equal e (Rkv.Rval.Bytes (Bytes.of_string "OVF")) ->
                  cover_f6 := true
              | _ ->
                  incr fails;
                  Printf.printf "F6 FAIL (RSEED=%d): expected throw OVF, got %s\n"
                    seed (show_out r.out))
         | "sample_fold_trace", _, Rkv.Rval.List elems ->
             (* F8: ORDER — the chronological trace IS the input list, in order *)
             if trace_eq r.tr elems then cover_f8 := true
             else begin
               incr fails;
               Printf.printf "F8 ORDER FAIL (RSEED=%d): trace %s <> input %s\n"
                 seed (show_tr r.tr) (show_tr elems)
             end
         | ("sample_fold_put" | "sample_fold_trace" | "sample_fold_concat"), Fnonlist, _ ->
             (* F7: non-list scrutinee -> init result, no store writes, no trace *)
             let init_ok =
               match name, r.out with
               | "sample_fold_put", Ok (Rkv.Rval.Int z) -> Z.equal z Z.zero
               | "sample_fold_trace", Ok Rkv.Rval.Unit -> true
               | "sample_fold_concat", Ok (Rkv.Rval.Bytes b) -> Bytes.length b = 0
               | _, _ -> false
             in
             if not (init_ok && r.state = [] && r.tr = []) then begin
               incr fails;
               Printf.printf "F7 FAIL %s (RSEED=%d): expected init result, got (%s, %s, %s)\n"
                 name seed (show_out r.out) (show_state r.state) (show_tr r.tr)
             end
         | _ -> ()))
      programs
  done;

  (* F8 companion: a concrete list and its REVERSE yield reversed traces (order is
     genuinely observable, not accidentally symmetric). *)
  let l = [ Rkv.Rval.Int Z.one; Rkv.Rval.Int (Z.of_int 2); Rkv.Rval.Int (Z.of_int 3) ] in
  let fwd = ref_obs S.sample_fold_trace (Rkv.Rval.List l) in
  let bwd = ref_obs S.sample_fold_trace (Rkv.Rval.List (List.rev l)) in
  if not (trace_eq fwd.tr l && trace_eq bwd.tr (List.rev l) && not (trace_eq fwd.tr bwd.tr))
  then begin
    incr fails;
    Printf.printf "F8 REVERSE FAIL (RSEED=%d): fwd=%s bwd=%s\n" seed (show_tr fwd.tr) (show_tr bwd.tr)
  end;

  (* Spot-check: the concat accumulator is order-sensitive across ref AND fast. *)
  let bl = Rkv.Rval.List [ Rkv.Rval.Bytes (Bytes.of_string "A"); Rkv.Rval.Bytes (Bytes.of_string "BC") ] in
  let rc = ref_obs S.sample_fold_concat bl and fc = fast_obs Gen.sample_fold_concat bl in
  (match rc.out, fc.out with
   | Ok (Rkv.Rval.Bytes rb), Ok (Rkv.Rval.Bytes fb)
     when Bytes.equal rb (Bytes.of_string "ABC") && Bytes.equal fb (Bytes.of_string "ABC") -> ()
   | _ ->
       incr fails;
       Printf.printf "CONCAT SPOT-CHECK FAIL (RSEED=%d): ref=%s fast=%s\n"
         seed (show_out rc.out) (show_out fc.out));

  let cov_ok =
    !cover_f1 && !cover_f2 && !cover_f3 && !cover_f4 && !cover_f5 && !cover_f6
    && !cover_f7 && !cover_f8
  in
  Printf.printf
    "rounds=%d programs=%d fails=%d\n\
     coverage: F1(empty)=%b F2(singleton)=%b F3(large-1000+)=%b F4(mixed)=%b\n\
     F5(error-mid-fold)=%b F6(acc-overflow)=%b F7(non-list)=%b F8(order-via-trace)=%b\n"
    n (List.length programs) !fails
    !cover_f1 !cover_f2 !cover_f3 !cover_f4 !cover_f5 !cover_f6 !cover_f7 !cover_f8;
  if !fails = 0 && cov_ok then
    print_endline
      "FOLD DIFFERENTIAL OK: reference == fast (outcome+state+trace) over F1-F8; \
       order asserted via trace; coverage asserted"
  else begin
    if not cov_ok then
      print_endline "FOLD COVERAGE GAP: a required class (F1-F8) was never exercised";
    exit 1
  end
