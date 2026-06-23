(** Trace-effect differential test: the append-only event log produced by the reference
    (the [trace] field of [world], chronological) must match the fast side (the [Trace.run]
    buffer wrapped around the KV handler), and the KV state must match too. For
    [sample_trace] (emit 10; put 1; emit 20) the trace is [10; 20] on both sides. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let z_of = Coqconv.z_of_coqz

let ref_obs (pairs : (Z.t * Z.t) list) : (Z.t * Z.t) list * Z.t list =
  let m0 =
    List.fold_left
      (fun m (k, v) -> E.M.add (Coqconv.coqz_of_z k) (E.DInt (Coqconv.coqz_of_z v)) m)
      E.M.empty pairs
  in
  let bindings, tr =
    match E.observe_full E.DUnit m0 S.sample_trace with
    | D.Coq_pair (D.Coq_pair (_o, bs), t) -> (bs, t)
  in
  let state =
    Coqconv.list_of_coq bindings
    |> List.map (fun p ->
           match p with
           | D.Coq_pair (k, E.DInt v) -> (z_of k, z_of v)
           | D.Coq_pair (_, _) -> failwith "reference: non-int KV value")
    |> List.sort (fun (a, _) (b, _) -> Z.compare a b)
  in
  let trace =
    Coqconv.list_of_coq tr
    |> List.map (function E.DInt z -> z_of z | _ -> failwith "reference: non-int trace event")
  in
  (state, trace)

let fast_obs (pairs : (Z.t * Z.t) list) : (Z.t * Z.t) list * Z.t list =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace table k v) pairs;
  let buf = ref [] in
  (* Trace handler outermost (Emit propagates out of the KV handler to it), KV inner. *)
  Rkv.Trace.run buf (fun () -> Rkv.Kv.run table (fun () -> ignore (Gen.sample_trace ())));
  (Rkv.Kv.observe table, Rkv.Trace.contents buf)

let list_eq eq a b = List.length a = List.length b && List.for_all2 eq a b
let state_eq = list_eq (fun (k1, v1) (k2, v2) -> Z.equal k1 k2 && Z.equal v1 v2)
let trace_eq = list_eq Z.equal

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260621
let rng = Random.State.make [| seed |]
let gen_state () = List.init (Random.State.int rng 8) (fun _ -> (Z.of_int (Random.State.int rng 12 - 2), Z.of_int (Random.State.int rng 1000)))
let show_tr l = "[" ^ String.concat "; " (List.map Z.to_string l) ^ "]"

let () =
  let n = 3000 in
  let fails = ref 0 and traced = ref 0 in
  for _ = 1 to n do
    let pairs = gen_state () in
    let rs, rt = ref_obs pairs and fs, ft = fast_obs pairs in
    if trace_eq rt [ Z.of_int 10; Z.of_int 20 ] then incr traced;
    if not (state_eq rs fs && trace_eq rt ft) then (
      incr fails;
      Printf.printf "MISMATCH (RSEED=%d) ref_trace=%s fast_trace=%s\n" seed (show_tr rt) (show_tr ft))
  done;
  Printf.printf "states=%d fails=%d | trace=[10;20] in %d/%d\n" n !fails !traced n;
  if !fails = 0 && !traced = n then
    print_endline "TRACE DIFFERENTIAL OK: event log matches in order; state matches"
  else (
    if !traced <> n then print_endline "TRACE: log was not [10;20] as expected";
    exit 1)
