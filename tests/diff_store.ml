(** Differential test for the expiring bytes-keyed store (R4, adr-0011).

    Runs the store samples (lifecycle, TTL boundary, put-clears-deadline, persist,
    setdeadline-on-missing) against the reference interpreter over adversarially seeded
    states — binary-hostile keys (collisions: same bytes different lengths, NUL-carrying,
    empty) and deadline-carrying entries — at adversarially chosen instants (the boundary
    d-1 / d / d+1 for every deadline in play, plus 0, negative, and 2^62). Outcome AND
    the live-filtered store observable must match.

    A DETERMINISTIC boundary block additionally asserts, per key, the oracle-validated
    rule live iff now <= d: a binding with deadline d is present at now = d-1, present at
    now = d (alive AT the deadline), absent at now = d+1 — on BOTH sides.

    Coverage is ASSERTED, not assumed:
      K1 same-prefix key collision ("a" vs "a\x00") in one state
      K2 NUL-carrying key            K3 empty key
      D1 live at d-1   D2 live AT d   D3 dead at d+1 (a seeded entry filtered out)
      P1 put-clears-deadline observed (DSome DNone)
      P2 setdeadline-on-missing observed false
      P3 delete returned true       P4 delete returned false (expired)

    Seeded and reproducible: set RSEED=<n> to replay; mismatches print the seed. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260711
let rng = Random.State.make [| seed |]

let two_pow_62 = Z.of_string "4611686018427387904"

(* --- observables ------------------------------------------------------------ *)

type entry = Rkv.Rval.t * Z.t option
type obs = { out : Rkv.Rval.t option; state : (bytes * entry) list }
(* [out]: Some v for ORet v; None only if the program threw (store samples never do). *)

let entry_eq ((v1, d1) : entry) ((v2, d2) : entry) =
  Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2

let state_eq a b =
  List.length a = List.length b
  && List.for_all2 (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2) a b

let obs_eq a b = Option.equal Rkv.Rval.equal a.out b.out && state_eq a.state b.state

let show_entry (v, dl) =
  Rkv.Rval.to_string v ^ (match dl with None -> "" | Some d -> "@" ^ Z.to_string d)

let show_obs o =
  Printf.sprintf "(%s, [%s])"
    (match o.out with None -> "throw" | Some v -> Rkv.Rval.to_string v)
    (String.concat "; "
       (List.map (fun (k, e) ->
            Printf.sprintf "%s=%s" (Rkv.Rval.to_string (Rkv.Rval.Bytes k)) (show_entry e))
          o.state))

(* --- reference side ---------------------------------------------------------- *)

let ref_obs (term : E.tm) (now : Z.t) (pairs : (bytes * entry) list) : obs =
  let m0 =
    List.fold_left
      (fun m (k, e) ->
         E.M.add (Coqconv.coq_string_of_bytes k) (Coqconv.coq_entry_of_rval e) m)
      E.M.empty pairs
  in
  let oc, bindings =
    match E.observe_full E.DUnit (Coqconv.coqz_of_z now) m0 term with
    | D.Coq_pair (D.Coq_pair (o, bs), _tr) -> (o, bs)
  in
  let out =
    match oc with E.ORet v -> Some (Coqconv.rval_of_dval v) | E.OErr _ -> None
  in
  let state =
    Coqconv.list_of_coq bindings
    |> List.map (fun p ->
           match p with
           | D.Coq_pair (k, e) ->
               (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
    |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)
  in
  { out; state }

(* --- fast side ---------------------------------------------------------------- *)

let fast_obs (fn : unit -> Rkv.Rval.t) (now : Z.t) (pairs : (bytes * entry) list) : obs =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, e) -> Rkv.Kv.T.replace table k e) pairs;
  let out =
    match Rkv.Runtime.with_store_and_time_checked ~source:(fun () -> now) table fn with
    | Ok v -> Some v
    | Error e -> failwith ("diff_store fast: " ^ Rkv.Kv.string_of_error e)
  in
  { out; state = Rkv.Kv.observe ~now table }

(* --- programs ----------------------------------------------------------------- *)

let programs : (string * E.tm * (unit -> Rkv.Rval.t)) list =
  [ ("sample_store", S.sample_store, Gen.sample_store);
    ("sample_ttl", S.sample_ttl, Gen.sample_ttl);
    ("sample_put_clears", S.sample_put_clears, Gen.sample_put_clears);
    ("sample_persist", S.sample_persist, Gen.sample_persist);
    ("sample_setdl_missing", S.sample_setdl_missing, Gen.sample_setdl_missing) ]

(* --- adversarial generators ---------------------------------------------------- *)

(* Key pool: collisions (shared prefixes, same bytes different lengths), NUL-carrying,
   empty, the sample keys themselves, and a large key. *)
let key_pool : bytes list =
  [ Bytes.empty;                       (* K3 *)
    Bytes.of_string "\x00";            (* K2 *)
    Bytes.of_string "a";
    Bytes.of_string "a\x00";           (* K1 vs "a" *)
    Bytes.of_string "a\x00b";
    Bytes.of_string "ab";
    Bytes.of_string "abc";
    Bytes.of_string "tk";              (* collides with sample_ttl / persist / put_clears *)
    Bytes.of_string "sk";              (* collides with sample_store *)
    Bytes.of_string "7";
    Bytes.make 300 'K' ]

let gen_key () = List.nth key_pool (Random.State.int rng (List.length key_pool))

let gen_value () : Rkv.Rval.t =
  match Random.State.int rng 4 with
  | 0 -> Rkv.Rval.Int (Z.of_int (Random.State.int rng 2000 - 1000))
  | 1 -> Rkv.Rval.Bytes (Bytes.of_string "v\x00\xff")
  | 2 -> Rkv.Rval.Bool (Random.State.bool rng)
  | _ -> Rkv.Rval.Int two_pow_62

(* Deadlines cluster on the boundary around the chosen [now] plus absolutes. *)
let gen_deadline (now : Z.t) : Z.t option =
  match Random.State.int rng 10 with
  | 0 -> None
  | 1 -> Some (Z.sub now Z.one)     (* already expired: d = now-1 -> D3 *)
  | 2 -> Some now                   (* alive AT the deadline -> D2 *)
  | 3 -> Some (Z.add now Z.one)     (* d = now+1 -> D1 *)
  | 4 -> Some Z.zero
  | 5 -> Some (Z.of_int (-7))
  | 6 -> Some two_pow_62
  | 7 -> Some (Z.of_int 1000)       (* the sample_ttl deadline *)
  | 8 -> Some (Z.of_int 500)        (* the sample_put_clears deadline *)
  | _ -> Some (Z.of_int (Random.State.int rng 2000))

(* Instants: the boundaries of every deadline the samples use, plus 0/negative/2^62. *)
let gen_now () : Z.t =
  match Random.State.int rng 13 with
  | 0 -> Z.of_int 999   | 1 -> Z.of_int 1000 | 2 -> Z.of_int 1001
  | 3 -> Z.of_int 499   | 4 -> Z.of_int 500  | 5 -> Z.of_int 501
  | 6 -> Z.of_int 799   | 7 -> Z.of_int 800  | 8 -> Z.of_int 801
  | 9 -> Z.zero         | 10 -> Z.of_int (-5) | 11 -> two_pow_62
  | _ -> Z.of_int (Random.State.int rng 3000 - 100)

let gen_state (now : Z.t) : (bytes * entry) list =
  let n = Random.State.int rng 8 in
  List.init n (fun _ -> (gen_key (), (gen_value (), gen_deadline now)))
  (* de-duplicate keys, last write wins — mirrors Hashtbl.replace/M.add *)
  |> List.fold_left (fun acc (k, e) ->
         (k, e) :: List.filter (fun (k', _) -> not (Bytes.equal k k')) acc) []

(* --- coverage ------------------------------------------------------------------ *)

let cov_k1 = ref false and cov_k2 = ref false and cov_k3 = ref false
let cov_d1 = ref false and cov_d2 = ref false and cov_d3 = ref false
let cov_p1 = ref false and cov_p2 = ref false and cov_p3 = ref false and cov_p4 = ref false

let note_state (now : Z.t) (pairs : (bytes * entry) list) (r : obs) =
  let has k = List.exists (fun (k', _) -> Bytes.equal k' (Bytes.of_string k)) pairs in
  if has "a" && has "a\x00" then cov_k1 := true;
  if List.exists (fun (k, _) -> Bytes.exists (fun c -> c = '\x00') k) pairs then
    cov_k2 := true;
  if has "" then cov_k3 := true;
  List.iter
    (fun (k, (_, dl)) ->
       match dl with
       | Some d ->
           let live_in_obs = List.exists (fun (k', _) -> Bytes.equal k k') r.state in
           if Z.equal d (Z.add now Z.one) && live_in_obs then cov_d1 := true;
           if Z.equal d now && live_in_obs then cov_d2 := true;
           if Z.equal d (Z.sub now Z.one) && not live_in_obs then cov_d3 := true
       | None -> ())
    pairs

let note_outcome (name : string) (r : obs) =
  match name, r.out with
  | "sample_put_clears", Some (Rkv.Rval.Some Rkv.Rval.None) -> cov_p1 := true
  | "sample_setdl_missing", Some (Rkv.Rval.Bool false) -> cov_p2 := true
  | "sample_ttl", Some (Rkv.Rval.Pair (_, Rkv.Rval.Pair (_, Rkv.Rval.Bool b))) ->
      if b then cov_p3 := true else cov_p4 := true
  | _ -> ()

(* --- deterministic per-key boundary block -------------------------------------- *)

(* For deadline d = 1000: seed one binding with that deadline; observe at d-1, d, d+1 on
   BOTH sides via a program that does not touch the key (sample_ret touches "6" only).
   Expectation: live, live (AT the deadline), absent. The mutant rule (<) dies here. *)
let boundary_block () : bool =
  let d = Z.of_int 1000 in
  let key = Bytes.of_string "bk" in
  let entry = (Rkv.Rval.Int (Z.of_int 7), Some d) in
  List.for_all
    (fun (now, expected_live) ->
       let r = ref_obs S.sample_ret now [ (key, entry) ] in
       let f = fast_obs Gen.sample_ret now [ (key, entry) ] in
       let present o = List.exists (fun (k, _) -> Bytes.equal k key) o.state in
       let ok = obs_eq r f && present r = expected_live && present f = expected_live in
       if not ok then
         Printf.printf
           "BOUNDARY FAIL (RSEED=%d) d=%s now=%s expected_live=%b\n  ref =%s\n  fast=%s\n"
           seed (Z.to_string d) (Z.to_string now) expected_live (show_obs r) (show_obs f);
       ok)
    [ (Z.of_int 999, true);    (* d-1: live *)
      (Z.of_int 1000, true);   (* d:   alive AT the deadline (now <= d) *)
      (Z.of_int 1001, false) ] (* d+1: dead *)

(* --- main ----------------------------------------------------------------------- *)

let () =
  let n = 3000 in
  let fails = ref 0 in
  for _ = 1 to n do
    let now = gen_now () in
    let pairs = gen_state now in
    List.iter
      (fun (name, term, fn) ->
        let r = ref_obs term now pairs and f = fast_obs fn now pairs in
        note_state now pairs r;
        note_outcome name r;
        if not (obs_eq r f) then (
          incr fails;
          Printf.printf "MISMATCH %s (RSEED=%d) now=%s\n  ref =%s\n  fast=%s\n"
            name seed (Z.to_string now) (show_obs r) (show_obs f)))
      programs
  done;
  let boundary_ok = boundary_block () in
  let cov_ok =
    !cov_k1 && !cov_k2 && !cov_k3 && !cov_d1 && !cov_d2 && !cov_d3
    && !cov_p1 && !cov_p2 && !cov_p3 && !cov_p4
  in
  Printf.printf
    "states=%d programs=%d fails=%d boundary(d-1/d/d+1)=%b | coverage: K1(collision)=%b K2(NUL-key)=%b K3(empty-key)=%b D1(live@d-1)=%b D2(live@d)=%b D3(dead@d+1)=%b P1(put-clears)=%b P2(setdl-missing)=%b P3(del-true)=%b P4(del-false)=%b\n"
    n (List.length programs) !fails boundary_ok
    !cov_k1 !cov_k2 !cov_k3 !cov_d1 !cov_d2 !cov_d3 !cov_p1 !cov_p2 !cov_p3 !cov_p4;
  if !fails = 0 && boundary_ok && cov_ok then
    print_endline
      "STORE DIFFERENTIAL OK: reference == fast on expiring store; boundary now<=d asserted per key"
  else (
    if not cov_ok then print_endline "STORE COVERAGE GAP: a required class (K/D/P) was never exercised";
    exit 1)
