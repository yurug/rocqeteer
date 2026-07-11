(** Differential test for the Time effect (R5, adr-0011).

    [sample_now] = ONow; PAddChecked now 1000 -> DPair now (now+1000), or DNone on
    overflow. The reference receives [now] as [run_top]'s instant; the fast side receives
    the SAME value from the injected source through the Time+Store composition point
    (Time outermost, one source instance — Runtime_SingleTimeSource_refines). The source
    is stepped only BETWEEN runs (the determinism protocol): within a run both sides see
    one instant.

    Asserted per run:
      (1) reference outcome == fast outcome (byte-identical Rval);
      (2) reference-now == fast-source-now: the [now] the program OBSERVED (the first
          pair component) equals the Z the source was built from, on both sides.

    Instant classes (coverage ASSERTED): zero, negative, the 2^62 boundary, a success
    (in-range add), and the int64_max overflow (DNone path).

    Seeded and reproducible: RSEED=<n> replays; mismatches print the seed. *)

module E = Ref_extracted.EffIR
module S = Ref_extracted.Samples
module D = Ref_extracted.Datatypes
module Gen = Generated.Prog0_generated

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260711
let rng = Random.State.make [| seed |]

let two_pow_62 = Z.of_string "4611686018427387904"
let int64_max = Z.of_string "9223372036854775807"
let int64_min = Z.of_string "-9223372036854775808"

(* --- reference side ---------------------------------------------------------- *)

let ref_outcome (now : Z.t) : Rkv.Rval.t =
  match E.run_top E.DUnit (Coqconv.coqz_of_z now) S.sample_now with
  | D.Coq_pair (E.ORet v, _) -> Coqconv.rval_of_dval v
  | D.Coq_pair (E.OErr e, _) ->
      failwith ("diff_time ref error: " ^ Rkv.Rval.to_string (Coqconv.rval_of_dval e))

(* --- fast side ---------------------------------------------------------------- *)

let fast_outcome (now : Z.t) : Rkv.Rval.t =
  let table = Rkv.Kv.T.create 4 in
  (* ONE source instance drives Time and the store; stepped only between runs. *)
  match Rkv.Runtime.with_store_and_time_checked ~source:(fun () -> now) table
          Gen.sample_now with
  | Ok v -> v
  | Error e -> failwith ("diff_time fast: " ^ Rkv.Kv.string_of_error e)

(* --- instants ----------------------------------------------------------------- *)

let gen_now () : Z.t =
  match Random.State.int rng 16 with
  | 0 -> Z.zero
  | 1 -> Z.of_int (-1)
  | 2 -> Z.of_int (-1000)
  | 3 -> Z.of_int 999
  | 4 -> two_pow_62                       (* the 2^62 boundary *)
  | 5 -> Z.sub two_pow_62 Z.one
  | 6 -> Z.add two_pow_62 Z.one
  | 7 -> int64_max                        (* overflow: now+1000 leaves int64 *)
  | 8 -> Z.sub int64_max (Z.of_int 1000)  (* exactly int64_max after the add *)
  | 9 -> Z.sub int64_max (Z.of_int 999)   (* first overflowing instant *)
  | 10 -> int64_min
  | _ -> Z.of_int (Random.State.int rng 2_000_000 - 1_000_000)

(* --- coverage ------------------------------------------------------------------ *)

let cov_zero = ref false and cov_neg = ref false and cov_262 = ref false
let cov_success = ref false and cov_overflow = ref false

let note (now : Z.t) (r : Rkv.Rval.t) =
  if Z.equal now Z.zero then cov_zero := true;
  if Z.sign now < 0 then cov_neg := true;
  if Z.equal now two_pow_62 then cov_262 := true;
  (match r with
   | Rkv.Rval.Pair (_, _) -> cov_success := true
   | Rkv.Rval.None -> cov_overflow := true
   | _ -> ())

(* --- main ----------------------------------------------------------------------- *)

let () =
  let n = 3000 in
  let fails = ref 0 and now_flow_fails = ref 0 in
  for _ = 1 to n do
    let now = gen_now () in
    let r = ref_outcome now and f = fast_outcome now in
    note now r;
    if not (Rkv.Rval.equal r f) then (
      incr fails;
      Printf.printf "MISMATCH (RSEED=%d) now=%s\n  ref =%s\n  fast=%s\n"
        seed (Z.to_string now) (Rkv.Rval.to_string r) (Rkv.Rval.to_string f));
    (* reference-now == fast-source-now: the observed instant is the injected one. *)
    let observed_ok (o : Rkv.Rval.t) =
      match o with
      | Rkv.Rval.Pair (Rkv.Rval.Int obs, Rkv.Rval.Int dl) ->
          Z.equal obs now && Z.equal dl (Z.add now (Z.of_int 1000))
      | Rkv.Rval.None ->
          (* overflow path: now+1000 must actually leave int64 range *)
          Z.gt (Z.add now (Z.of_int 1000)) int64_max
          || Z.lt (Z.add now (Z.of_int 1000)) int64_min
      | _ -> false
    in
    if not (observed_ok r && observed_ok f) then (
      incr now_flow_fails;
      Printf.printf "NOW-FLOW FAIL (RSEED=%d) now=%s ref=%s fast=%s\n"
        seed (Z.to_string now) (Rkv.Rval.to_string r) (Rkv.Rval.to_string f))
  done;
  let cov_ok = !cov_zero && !cov_neg && !cov_262 && !cov_success && !cov_overflow in
  Printf.printf
    "runs=%d fails=%d now-flow-fails=%d | coverage: zero=%b negative=%b 2^62=%b success=%b overflow=%b\n"
    n !fails !now_flow_fails !cov_zero !cov_neg !cov_262 !cov_success !cov_overflow;
  if !fails = 0 && !now_flow_fails = 0 && cov_ok then
    print_endline
      "TIME DIFFERENTIAL OK: injected instant flows identically; reference-now == fast-source-now per run"
  else (
    if not cov_ok then print_endline "TIME COVERAGE GAP: an instant class was never exercised";
    exit 1)
