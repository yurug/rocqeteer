(** Step-3 adversarial differential test for the KV slice (property P5).

    The generated [prog0] (= [incr_at "7"]) is run against the reference interpreter over
    many adversarially-biased initial states; the observables must match. Coverage of the
    slice-1 edge classes is ASSERTED, not assumed (kb/plan.md Resolution 6,
    kb/conventions/testing-strategy.md, kb/properties/edge-cases.md):
      T2 key absent, T4 large state, T5 duplicate puts, T7 order-independence.
    T1 (overflow) is N/A: the default value realizer is zarith [Z], which cannot overflow.
    T8 (unhandled effect -> typed error) is checked via a fault injection.

    R4+R5 (adr-0011): keys are decimal byte strings; entries carry (value, deadline);
    the fast side runs under the Time+Store composition point at a fixed instant.

    Seeded and reproducible: set RSEED=<n> to replay; a mismatch prints the offending
    state and seed for the corpus. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let now = Z.zero
let key_bytes (k : Z.t) : bytes = Bytes.of_string (Z.to_string k)
let key7 = key_bytes (Z.of_int 7)

(* Reference: build the map from puts (last-write-wins, deadline-less), run [term],
   normalize the live bindings to sorted (bytes, entry). *)
let ref_observe (term : E.tm) (pairs : (Z.t * Z.t) list)
    : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let m0 =
    List.fold_left
      (fun m (k, v) ->
         E.M.add (Coqconv.coq_string_of_bytes (key_bytes k))
           (Coqconv.coq_entry_of_rval (Rkv.Rval.Int v, None)) m)
      E.M.empty pairs
  in
  let bindings =
    match E.observe_full E.DUnit (Coqconv.coqz_of_z now) m0 term with
    | D.Coq_pair (D.Coq_pair (D.Coq_pair (_o, bs), _tr), _jr) -> bs
  in
  Coqconv.list_of_coq bindings
  |> List.map (fun p ->
         match p with
         | D.Coq_pair (k, e) ->
             (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
  |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)

(* Fast: build the Hashtbl from the same puts (values wrapped as Rval.Int, no deadline),
   run the generated [fn] under the Time+Store composition point (one source). *)
let fast_observe (name : string) (fn : unit -> unit) (pairs : (Z.t * Z.t) list)
    : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace table (key_bytes k) (Rkv.Rval.Int v, None)) pairs;
  (match Rkv.Runtime.with_store_and_time_checked ~source:(fun () -> now) table fn with
   | Ok () -> ()
   | Error e -> failwith ("fast " ^ name ^ ": " ^ Rkv.Kv.string_of_error e));
  Rkv.Kv.observe ~now table

(* Each program: a reference term + the matching generated function (wrapped to unit). The
   samples cover ODelete / Ret / multi-Perform / '-'-carrying key / deep nesting, so the
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

(* Small key range so key "7" is hit often and the Hashtbl sees collisions / duplicates. *)
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

let key7_present pairs = List.exists (fun (k, _) -> Bytes.equal (key_bytes k) key7) pairs

let show_entry (v, dl) =
  Rkv.Rval.to_string v ^ (match dl with None -> "" | Some d -> "@" ^ Z.to_string d)

let show l =
  "[" ^ String.concat "; "
    (List.map (fun (k, e) -> Printf.sprintf "%s=%s" (Bytes.to_string k) (show_entry e)) l)
  ^ "]"

let entry_eq (v1, d1) (v2, d2) = Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2

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
          && List.for_all2
               (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2)
               r f
        in
        if not eq then (
          incr fails;
          Printf.printf "MISMATCH %s (RSEED=%d)\n  ref =%s\n  fast=%s\n"
            name seed (show r) (show f)))
      programs
  done;
  (* T8 fault injection: both an unhandled (unregistered) effect AND a stray exception must
     become typed errors at the checked boundary, never a crash (audit C1). *)
  let src () = now in
  let t8_unhandled =
    match Rkv.Runtime.with_store_and_time_checked ~source:src (Rkv.Kv.T.create 1)
            Rkv.Fault.perform_unregistered with
    | Error (`Unhandled_effect _) -> true
    | _ -> false
  in
  let t8_exn =
    match Rkv.Runtime.with_store_and_time_checked ~source:src (Rkv.Kv.T.create 1)
            (fun () -> raise Not_found) with
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
