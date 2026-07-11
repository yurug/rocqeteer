(** Error-effect differential test: for programs that may THROW, the reference outcome
    (ORet / OErr e) and final state must match the fast side's (Ok / Error e) and table —
    i.e. a throw aborts identically and commits exactly the pre-throw writes.

    This is the Error slice's P5: it checks the short-circuit semantics the KV-only diff
    cannot (kb/spec/reference-semantics.md, kb/conventions/error-handling.md).

    R4+R5 (adr-0011): keys are decimal byte strings; entries carry (value, deadline);
    the fast side runs under Err ∘ Time ∘ Store (one time source). *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let now = Z.zero
let key_bytes (k : Z.t) : bytes = Bytes.of_string (Z.to_string k)

(* An observation: the error outcome (None = returned normally; Some e = aborted) + state. *)
type obs = { err : Rkv.Rval.t option; state : (bytes * (Rkv.Rval.t * Z.t option)) list }

let ref_obs (term : E.tm) (pairs : (Z.t * Z.t) list) : obs =
  let m0 =
    List.fold_left
      (fun m (k, v) ->
         E.M.add (Coqconv.coq_string_of_bytes (key_bytes k))
           (Coqconv.coq_entry_of_rval (Rkv.Rval.Int v, None)) m)
      E.M.empty pairs
  in
  let oc, bindings =
    match E.observe_full E.DUnit (Coqconv.coqz_of_z now) m0 term with
    | D.Coq_pair (D.Coq_pair (o, bs), _tr) -> (o, bs)
  in
  let err =
    match oc with
    | E.ORet _ -> None
    | E.OErr d -> Some (Coqconv.rval_of_dval d)
  in
  let state =
    Coqconv.list_of_coq bindings
    |> List.map (fun p ->
           match p with
           | D.Coq_pair (k, e) ->
               (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
    |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)
  in
  { err; state }

let fast_obs (fn : unit -> unit) (pairs : (Z.t * Z.t) list) : obs =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace table (key_bytes k) (Rkv.Rval.Int v, None)) pairs;
  (* run_error catches a throw; the store handler interprets state up to that point. *)
  let err =
    match Rkv.Err.run_error (fun () ->
        Rkv.Runtime.with_store_and_time ~source:(fun () -> now) table fn) with
    | Ok () -> None
    | Error e -> Some e
  in
  { err; state = Rkv.Kv.observe ~now table }

let err_eq a b =
  match (a, b) with
  | None, None -> true
  | Some x, Some y -> Rkv.Rval.equal x y
  | _ -> false

let entry_eq (v1, d1) (v2, d2) = Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2

let state_eq a b =
  List.length a = List.length b
  && List.for_all2
       (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2)
       a b

let programs : (string * E.tm * (unit -> unit)) list =
  [ ("sample_throw", S.sample_throw, fun () -> ignore (Gen.sample_throw ()));
    ("sample_guard5", S.sample_guard5, fun () -> ignore (Gen.sample_guard5 ())) ]

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260621
let rng = Random.State.make [| seed |]
let gen_key () = Z.of_int (Random.State.int rng 12 - 2) (* small range incl. 5 *)
let gen_val () = Z.of_int (Random.State.int rng 1000 - 500)
let gen_state () =
  List.init (Random.State.int rng 8) (fun _ -> (gen_key (), gen_val ()))

let show_entry (v, dl) =
  Rkv.Rval.to_string v ^ (match dl with None -> "" | Some d -> "@" ^ Z.to_string d)

let show l =
  "[" ^ String.concat "; "
    (List.map (fun (k, e) -> Printf.sprintf "%s=%s" (Bytes.to_string k) (show_entry e)) l)
  ^ "]"
let show_err = function
  | None   -> "ok"
  | Some e -> "throw " ^ Rkv.Rval.to_string e

let () =
  let n = 3000 in
  let fails = ref 0 and threw = ref 0 and returned = ref 0 in
  for _ = 1 to n do
    let pairs = gen_state () in
    List.iter
      (fun (name, term, fn) ->
        let r = ref_obs term pairs and f = fast_obs fn pairs in
        (* coverage: did sample_guard5 take the throw path or the return path? *)
        if name = "sample_guard5" then
          (if r.err = None then incr returned else incr threw);
        if not (err_eq r.err f.err && state_eq r.state f.state) then (
          incr fails;
          Printf.printf "MISMATCH %s (RSEED=%d)\n  ref =(%s,%s)\n  fast=(%s,%s)\n"
            name seed
            (show_err r.err) (show r.state)
            (show_err f.err) (show f.state)))
      programs
  done;
  let cov_ok = !threw > 0 && !returned > 0 in
  Printf.printf "states=%d programs=%d fails=%d | guard5: threw=%d returned=%d\n"
    n (List.length programs) !fails !threw !returned;
  if !fails = 0 && cov_ok then
    print_endline "ERROR DIFFERENTIAL OK: throw aborts identically; both paths covered"
  else (
    if not cov_ok then print_endline "COVERAGE GAP: guard5 did not exercise both throw and return";
    exit 1)
