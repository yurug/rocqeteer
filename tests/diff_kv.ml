(** Step-3 adversarial differential test for the KV slice (property P5).

    The generated [prog0] (= [incr_at 7]) is run against the reference interpreter over
    many adversarially-biased initial states; the observables must match. Coverage of the
    slice-1 edge classes is ASSERTED, not assumed (kb/plan.md Resolution 6,
    kb/conventions/testing-strategy.md, kb/properties/edge-cases.md):
      T2 key absent, T4 large state, T5 duplicate puts, T7 order-independence.
    T1 (overflow) is N/A: the default value realizer is zarith [Z], which cannot overflow.
    T8 (unhandled effect -> typed error) is checked via a fault injection.

    Seeded and reproducible: set RSEED=<n> to replay; a mismatch prints the offending
    state and seed for the corpus. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let key7 = Z.of_int 7

(* Reference: build the map from puts (last-write-wins), run [term], normalize to sorted Z. *)
let ref_observe (term : E.tm) (pairs : (Z.t * Z.t) list) : (Z.t * Z.t) list =
  let m0 =
    List.fold_left
      (fun m (k, v) -> E.M.add (Coqconv.coqz_of_z k) (E.DInt (Coqconv.coqz_of_z v)) m)
      E.M.empty pairs
  in
  let bindings =
    match E.observe_full E.DUnit m0 term with D.Coq_pair (D.Coq_pair (_o, bs), _tr) -> bs
  in
  Coqconv.list_of_coq bindings
  |> List.map (fun p ->
         match p with
         | D.Coq_pair (k, E.DInt v) -> (Coqconv.z_of_coqz k, Coqconv.z_of_coqz v)
         | D.Coq_pair (_, _) -> failwith "reference produced a non-int KV value")
  |> List.sort (fun (a, _) (b, _) -> Z.compare a b)

(* Fast: build the Hashtbl from the same puts, run the generated [fn] under the handler. *)
let fast_observe (name : string) (fn : unit -> unit) (pairs : (Z.t * Z.t) list) : (Z.t * Z.t) list =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace table k v) pairs;
  (match Rkv.Kv.run_checked table fn with
   | Ok () -> ()
   | Error e -> failwith ("fast " ^ name ^ ": " ^ Rkv.Kv.string_of_error e));
  Rkv.Kv.observe table

(* Each program: a reference term + the matching generated function (wrapped to unit). The
   samples cover ODelete / Ret / multi-Perform / negative literal / deep nesting, so the
   differential harness exercises every codegen lowering rule, not just prog0's (finding 1). *)
let programs : (string * E.tm * (unit -> unit)) list =
  [ ("prog0", E.prog0, fun () -> ignore (Gen.prog0 ()));
    ("sample_delete", S.sample_delete, fun () -> ignore (Gen.sample_delete ()));
    ("sample_two", S.sample_two, fun () -> ignore (Gen.sample_two ()));
    ("sample_ret", S.sample_ret, fun () -> ignore (Gen.sample_ret ()));
    ("sample_neg", S.sample_neg, fun () -> ignore (Gen.sample_neg ()));
    ("sample_nested", S.sample_nested, fun () -> ignore (Gen.sample_nested ()));
    ("sample_count", S.sample_count, fun () -> ignore (Gen.sample_count ())) ]

(* --- adversarial, seeded generators (bias toward the edge classes above) --- *)
let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260621
let rng = Random.State.make [| seed |]

(* Small key range so key 7 is hit often and the Hashtbl sees collisions / duplicates. *)
let gen_key () = Z.of_int (Random.State.int rng 16 - 4)

let gen_val () =
  match Random.State.int rng 12 with
  | 0 -> Z.zero
  | 1 -> Z.of_int max_int
  | 2 -> Z.neg (Z.of_int max_int)
  | 3 -> Z.of_string "123456789012345678901234567890" (* beyond any fixed width *)
  | _ -> Z.of_int (Random.State.int rng 2000 - 1000)

let gen_state () =
  let n =
    match Random.State.int rng 10 with
    | 9 -> 60 + Random.State.int rng 80 (* large state, T4 *)
    | _ -> Random.State.int rng 8
  in
  List.init n (fun _ -> (gen_key (), gen_val ()))

let has_dup pairs =
  let ks = List.map fst pairs in
  List.length ks <> List.length (List.sort_uniq Z.compare ks)

let key7_present pairs = List.exists (fun (k, _) -> Z.equal k key7) pairs

let show l =
  "[" ^ String.concat "; " (List.map (fun (k, v) -> Printf.sprintf "%s=%s" (Z.to_string k) (Z.to_string v)) l) ^ "]"

let () =
  let n = 5000 in
  let fails = ref 0 and c7abs = ref 0 and c7pres = ref 0 and clarge = ref 0 and cdup = ref 0 in
  for _ = 1 to n do
    let pairs = gen_state () in
    if key7_present pairs then incr c7pres else incr c7abs;
    if List.length pairs >= 60 then incr clarge;
    if has_dup pairs then incr cdup;
    (* Every program is compared against the reference on this same state. *)
    List.iter
      (fun (name, term, fn) ->
        let r = ref_observe term pairs and f = fast_observe name fn pairs in
        let eq =
          List.length r = List.length f
          && List.for_all2 (fun (k1, v1) (k2, v2) -> Z.equal k1 k2 && Z.equal v1 v2) r f
        in
        if not eq then (
          incr fails;
          Printf.printf "MISMATCH %s (RSEED=%d) state=%s\n  ref =%s\n  fast=%s\n" name seed (show pairs)
            (show r) (show f)))
      programs
  done;
  (* T8 fault injection: both an unhandled (unregistered) effect AND a stray exception must
     become typed errors at the checked boundary, never a crash (audit C1). *)
  let t8_unhandled =
    match Rkv.Kv.run_checked (Rkv.Kv.T.create 1) Rkv.Fault.perform_unregistered with
    | Error (`Unhandled_effect _) -> true
    | _ -> false
  in
  let t8_exn =
    match Rkv.Kv.run_checked (Rkv.Kv.T.create 1) (fun () -> raise Not_found) with
    | Error (`Unexpected_exception _) -> true
    | _ -> false
  in
  let t8_ok = t8_unhandled && t8_exn in
  let cov_ok = !c7abs > 0 && !c7pres > 0 && !clarge > 0 && !cdup > 0 in
  Printf.printf
    "states=%d programs=%d comparisons=%d fails=%d | coverage: T2(7-absent)=%d 7-present=%d T4(large)=%d T5(dup-keys)=%d | T8=%b\n"
    n (List.length programs) (n * List.length programs) !fails !c7abs !c7pres !clarge !cdup t8_ok;
  if !fails = 0 && cov_ok && t8_ok then
    print_endline "STEP3 DIFFERENTIAL OK: reference == fast over adversarial states; coverage + T8 asserted"
  else (
    if not cov_ok then print_endline "COVERAGE GAP: a required edge class (T2/T4/T5) was never generated";
    if not t8_ok then print_endline "T8 FAIL: unhandled effect did not become a typed error";
    exit 1)
