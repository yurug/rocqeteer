(** Trace-effect differential test: the append-only event log produced by the reference
    (the [trace] field of [world], chronological) must match the fast side (the [Trace.run]
    buffer wrapped around the Time+Store stack), and the store state must match too. For
    [sample_trace] (emit 10; put "1"; emit 20) the trace is [10; 20] on both sides.

    R4+R5 (adr-0011): keys are decimal byte strings; entries carry (value, deadline). *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let now = Z.zero
let key_bytes (k : Z.t) : bytes = Bytes.of_string (Z.to_string k)

let ref_obs (pairs : (Z.t * Z.t) list)
    : (bytes * (Rkv.Rval.t * Z.t option)) list * Rkv.Rval.t list =
  let m0 =
    List.fold_left
      (fun m (k, v) ->
         E.M.add (Coqconv.coq_string_of_bytes (key_bytes k))
           (Coqconv.coq_entry_of_rval (Rkv.Rval.Int v, None)) m)
      E.M.empty pairs
  in
  let bindings, tr =
    match E.observe_full E.DUnit (Coqconv.coqz_of_z now) m0 S.sample_trace with
    | D.Coq_pair (D.Coq_pair (_o, bs), t) -> (bs, t)
  in
  let state =
    Coqconv.list_of_coq bindings
    |> List.map (fun p ->
           match p with
           | D.Coq_pair (k, e) ->
               (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
    |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)
  in
  let trace =
    Coqconv.list_of_coq tr |> List.map Coqconv.rval_of_dval
  in
  (state, trace)

let fast_obs (pairs : (Z.t * Z.t) list)
    : (bytes * (Rkv.Rval.t * Z.t option)) list * Rkv.Rval.t list =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace table (key_bytes k) (Rkv.Rval.Int v, None)) pairs;
  let buf = ref [] in
  (* Trace handler outermost (Emit propagates out of the Time+Store stack to it). *)
  Rkv.Trace.run buf (fun () ->
      Rkv.Runtime.with_store_and_time ~source:(fun () -> now) table
        (fun () -> ignore (Gen.sample_trace ())));
  (Rkv.Kv.observe ~now table, Rkv.Trace.contents buf)

let list_eq eq a b = List.length a = List.length b && List.for_all2 eq a b
let entry_eq (v1, d1) (v2, d2) = Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2
let state_eq = list_eq (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2)
let trace_eq = list_eq Rkv.Rval.equal

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260621
let rng = Random.State.make [| seed |]
let gen_state () =
  List.init (Random.State.int rng 8)
    (fun _ -> (Z.of_int (Random.State.int rng 12 - 2), Z.of_int (Random.State.int rng 1000)))

let show_tr l =
  "[" ^ String.concat "; " (List.map Rkv.Rval.to_string l) ^ "]"

let () =
  let n = 3000 in
  let fails = ref 0 and traced = ref 0 in
  for _ = 1 to n do
    let pairs = gen_state () in
    let rs, rt = ref_obs pairs and fs, ft = fast_obs pairs in
    if trace_eq rt [ Rkv.Rval.Int (Z.of_int 10); Rkv.Rval.Int (Z.of_int 20) ]
    then incr traced;
    if not (state_eq rs fs && trace_eq rt ft) then (
      incr fails;
      Printf.printf "MISMATCH (RSEED=%d) ref_trace=%s fast_trace=%s\n"
        seed (show_tr rt) (show_tr ft))
  done;
  Printf.printf "states=%d fails=%d | trace=[10;20] in %d/%d\n" n !fails !traced n;
  if !fails = 0 && !traced = n then
    print_endline "TRACE DIFFERENTIAL OK: event log matches in order; state matches"
  else (
    if !traced <> n then print_endline "TRACE: log was not [10;20] as expected";
    exit 1)
