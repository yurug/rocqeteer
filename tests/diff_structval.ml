(** Differential test for structured values (IR v2 R7, adr-0010-structured-values).

    Two parts:
    1. Reference-vs-generated differential over [sample_tag_build] (builds DTag/DPair/
       DList) and [sample_tag_dispatch] (matches on DTag via PTag), across adversarially
       biased contexts.
    2. DIRECT coqconv bridge round-trip: [dval_of_rval (rval_of_dval d) = d] for
       adversarially constructed structured [dval]s that never go through a sample
       program at all (deep nesting, empty/large/mixed-shape lists, Z-boundary tags).

    Adversarial classes (each must be covered; coverage is ASSERTED):
      S1  tag collision: same payload, tags 0 vs 1 (both dispatch + bridge)
      S2  deep nesting: Tag over Pair over List over Some
      S3  empty list
      S4  large list (>= 1000 elements)
      S5  mixed-shape list (Int/Bytes/Bool/Unit/Option/Pair/Tag together)
      S6  tag Z boundaries: 0, 1, 2^62, negative
      S7  dispatch: right-shaped payload, WRONG tag -> default
      S8  dispatch: context is not a DTag at all -> default
      S9  random fuzzed nested dval round-trip

    Seeds are logged; every counterexample prints its seed for corpus replay. *)

module E   = Ref_extracted.EffIR
module D   = Ref_extracted.Datatypes
module S   = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260711
let rng = Random.State.make [| seed |]

let int64_max = Z.of_string "9223372036854775807"
let int64_min = Z.of_string "-9223372036854775808"
let two_pow_62 = Z.of_string "4611686018427387904"

(* --- part 1a: sample_tag_build, reference vs generated --------------------- *)

let ref_tag_build (ctx : Z.t) : Rkv.Rval.t =
  match E.run_top (E.DInt (Coqconv.coqz_of_z ctx)) (Coqconv.coqz_of_z Z.zero) S.sample_tag_build with
  | D.Coq_pair (E.ORet v, _) -> Coqconv.rval_of_dval v
  | D.Coq_pair (E.OErr e, _) ->
      failwith ("diff_structval tag_build ref error: " ^ Rkv.Rval.to_string (Coqconv.rval_of_dval e))

let fast_tag_build (ctx : Z.t) : Rkv.Rval.t =
  let result = ref Rkv.Rval.None in
  Rkv.Env.run (Rkv.Rval.Int ctx) (fun () -> result := Gen.sample_tag_build ());
  !result

let gen_build_ctx () : Z.t =
  match Random.State.int rng 6 with
  | 0 -> int64_max
  | 1 -> int64_min
  | 2 -> Z.zero
  | 3 -> two_pow_62
  | _ -> Z.of_int (Random.State.int rng 2001 - 1000)

let build_fails = ref 0

let () =
  for _ = 1 to 2000 do
    let ctx = gen_build_ctx () in
    let r = ref_tag_build ctx and f = fast_tag_build ctx in
    if not (Rkv.Rval.equal r f) then begin
      incr build_fails;
      Printf.printf "TAG_BUILD MISMATCH (RSEED=%d) ctx=%s\n  ref=%s\n  fast=%s\n"
        seed (Z.to_string ctx) (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
    end
  done

(* --- part 1b: sample_tag_dispatch, reference vs generated ------------------ *)

let ref_tag_dispatch (ctx : Rkv.Rval.t) : Rkv.Rval.t =
  match E.run_top (Coqconv.dval_of_rval ctx) (Coqconv.coqz_of_z Z.zero) S.sample_tag_dispatch with
  | D.Coq_pair (E.ORet v, _) -> Coqconv.rval_of_dval v
  | D.Coq_pair (E.OErr e, _) ->
      failwith ("diff_structval tag_dispatch ref error: " ^ Rkv.Rval.to_string (Coqconv.rval_of_dval e))

let fast_tag_dispatch (ctx : Rkv.Rval.t) : Rkv.Rval.t =
  let result = ref Rkv.Rval.None in
  Rkv.Env.run ctx (fun () -> result := Gen.sample_tag_dispatch ());
  !result

let tg0 = Bytes.of_string "TG0"
let tg1 = Bytes.of_string "TG1"
let tdf = Bytes.of_string "TDF"

let gen_payload () : Rkv.Rval.t =
  match Random.State.int rng 4 with
  | 0 -> Rkv.Rval.Int (gen_build_ctx ())
  | 1 ->
      Rkv.Rval.Bytes
        (Bytes.init (Random.State.int rng 8) (fun _ -> Char.chr (Random.State.int rng 256)))
  | 2 -> Rkv.Rval.Unit
  | _ -> Rkv.Rval.Bool (Random.State.bool rng)

(* Coverage tags for the dispatch loop (assigned while generating so we know, per
   iteration, which class we are about to exercise). *)
type dispatch_class = Tag0 | Tag1 | WrongTag | BoundaryTag | NonTag

let gen_dispatch_ctx () : dispatch_class * Rkv.Rval.t =
  match Random.State.int rng 8 with
  | 0 -> (Tag0, Rkv.Rval.Tag (Z.zero, gen_payload ()))
  | 1 -> (Tag1, Rkv.Rval.Tag (Z.one, gen_payload ()))
  | 2 -> (WrongTag, Rkv.Rval.Tag (Z.of_int 7, gen_payload ()))
  | 3 -> (BoundaryTag, Rkv.Rval.Tag (two_pow_62, gen_payload ()))
  | 4 -> (BoundaryTag, Rkv.Rval.Tag (Z.of_int (-3), gen_payload ()))
  | 5 -> (NonTag, gen_payload ())
  | 6 -> (NonTag, Rkv.Rval.List [ gen_payload (); gen_payload () ])
  | _ -> (NonTag, Rkv.Rval.Pair (gen_payload (), gen_payload ()))

let cover_s1_tag0 = ref false
let cover_s1_tag1 = ref false
let cover_s7 = ref false
let cover_s8 = ref false
let cover_s6_dispatch = ref false

let dispatch_fails = ref 0

let () =
  for _ = 1 to 3000 do
    let (cls, ctx) = gen_dispatch_ctx () in
    (match cls with
     | Tag0 -> cover_s1_tag0 := true
     | Tag1 -> cover_s1_tag1 := true
     | WrongTag -> cover_s7 := true
     | BoundaryTag -> cover_s6_dispatch := true
     | NonTag -> cover_s8 := true);
    let r = ref_tag_dispatch ctx and f = fast_tag_dispatch ctx in
    if not (Rkv.Rval.equal r f) then begin
      incr dispatch_fails;
      Printf.printf "TAG_DISPATCH MISMATCH (RSEED=%d) ctx=%s\n  ref=%s\n  fast=%s\n"
        seed (Rkv.Rval.to_string ctx) (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
    end;
    let expect_branch_ok =
      match cls with
      | Tag0 -> Rkv.Rval.equal r (Rkv.Rval.Bytes tg0)
      | Tag1 -> Rkv.Rval.equal r (Rkv.Rval.Bytes tg1)
      | WrongTag | BoundaryTag | NonTag -> Rkv.Rval.equal r (Rkv.Rval.Bytes tdf)
    in
    if not expect_branch_ok then begin
      incr dispatch_fails;
      Printf.printf "TAG_DISPATCH BRANCH FAIL (RSEED=%d): unexpected result %s\n"
        seed (Rkv.Rval.to_string r)
    end
  done

(* --- part 2: DIRECT coqconv bridge round-trip ------------------------------ *)

let mk_bytes (s : string) : E.dval =
  E.DBytes (Coqconv.bytes_to_ascii_list (Bytes.of_string s))

let bridge_fails = ref 0

let check_roundtrip (label : string) (d : E.dval) =
  let r = Coqconv.rval_of_dval d in
  let d' = Coqconv.dval_of_rval r in
  if d' <> d then begin
    incr bridge_fails;
    Printf.printf "BRIDGE MISMATCH (RSEED=%d) %s\n  rval=%s\n" seed label (Rkv.Rval.to_string r)
  end

let cover_s1 = ref false
let cover_s2 = ref false
let cover_s3 = ref false
let cover_s4 = ref false
let cover_s5 = ref false
let cover_s6 = ref false
let cover_s9 = ref false

(* S1: tag collision — same payload, different tags, round-tripped independently *)
let () =
  let p = E.DInt (Coqconv.coqz_of_z (Z.of_int 42)) in
  check_roundtrip "S1 tag0" (E.DTag (Coqconv.coqz_of_z Z.zero, p));
  check_roundtrip "S1 tag1" (E.DTag (Coqconv.coqz_of_z Z.one, p));
  cover_s1 := true

(* S2: deep nesting — Tag over Pair over List over Some *)
let () =
  let inner = E.DSome (E.DInt (Coqconv.coqz_of_z (Z.of_int 7))) in
  let lst =
    E.DList (Coqconv.coq_list_of [ E.DInt (Coqconv.coqz_of_z Z.one); mk_bytes "x"; inner ])
  in
  let pair = E.DPair (lst, inner) in
  let d = E.DTag (Coqconv.coqz_of_z (Z.of_int 3), pair) in
  check_roundtrip "S2 deep-nesting" d;
  cover_s2 := true

(* S3: empty list *)
let () =
  check_roundtrip "S3 empty-list" (E.DList (Coqconv.coq_list_of []));
  cover_s3 := true

(* S4: large list (>= 1000 elements) *)
let () =
  let elems =
    List.init 1200 (fun i ->
        if i mod 2 = 0 then E.DInt (Coqconv.coqz_of_z (Z.of_int i)) else mk_bytes (string_of_int i))
  in
  check_roundtrip "S4 large-list" (E.DList (Coqconv.coq_list_of elems));
  cover_s4 := true

(* S5: mixed-shape list (Int/Bytes/Bool/Unit/Option/Pair/Tag together) *)
let () =
  let elems =
    [ E.DInt (Coqconv.coqz_of_z (Z.of_int 1));
      mk_bytes "y";
      E.DBool Ref_extracted.Datatypes.Coq_true;
      E.DUnit;
      E.DSome (E.DInt (Coqconv.coqz_of_z (Z.of_int 2)));
      E.DNone;
      E.DPair (E.DInt (Coqconv.coqz_of_z Z.one), E.DInt (Coqconv.coqz_of_z (Z.of_int 2)));
      E.DTag (Coqconv.coqz_of_z (Z.of_int 9), E.DInt (Coqconv.coqz_of_z (Z.of_int 3))) ]
  in
  check_roundtrip "S5 mixed-shape-list" (E.DList (Coqconv.coq_list_of elems));
  cover_s5 := true

(* S6: tag Z boundaries *)
let () =
  let p = mk_bytes "z" in
  check_roundtrip "S6 tag-zero" (E.DTag (Coqconv.coqz_of_z Z.zero, p));
  check_roundtrip "S6 tag-one" (E.DTag (Coqconv.coqz_of_z Z.one, p));
  check_roundtrip "S6 tag-2^62" (E.DTag (Coqconv.coqz_of_z two_pow_62, p));
  check_roundtrip "S6 tag-negative" (E.DTag (Coqconv.coqz_of_z (Z.of_int (-17)), p));
  cover_s6 := true

(* S9: random fuzzed nested dval, depth-bounded so it terminates and stays small
   enough per instance while still exercising deep Tag/Pair/List/Some nesting. *)
let rec gen_random_dval (depth : int) : E.dval =
  if depth <= 0 then
    match Random.State.int rng 4 with
    | 0 -> E.DUnit
    | 1 -> E.DInt (Coqconv.coqz_of_z (gen_build_ctx ()))
    | 2 ->
        mk_bytes
          (String.init (Random.State.int rng 6) (fun _ -> Char.chr (32 + Random.State.int rng 95)))
    | _ ->
        E.DBool
          (if Random.State.bool rng then Ref_extracted.Datatypes.Coq_true
           else Ref_extracted.Datatypes.Coq_false)
  else
    match Random.State.int rng 6 with
    | 0 -> E.DSome (gen_random_dval (depth - 1))
    | 1 -> E.DNone
    | 2 -> E.DPair (gen_random_dval (depth - 1), gen_random_dval (depth - 1))
    | 3 -> E.DTag (Coqconv.coqz_of_z (gen_build_ctx ()), gen_random_dval (depth - 1))
    | 4 ->
        let n = Random.State.int rng 5 in
        E.DList (Coqconv.coq_list_of (List.init n (fun _ -> gen_random_dval (depth - 1))))
    | _ -> gen_random_dval 0

let () =
  for _ = 1 to 2000 do
    check_roundtrip "S9 fuzz" (gen_random_dval 4)
  done;
  cover_s9 := true

(* --- summary ----------------------------------------------------------------- *)

let () =
  let cov_ok =
    !cover_s1 && !cover_s1_tag0 && !cover_s1_tag1 && !cover_s2 && !cover_s3 && !cover_s4
    && !cover_s5 && !cover_s6 && !cover_s6_dispatch && !cover_s7 && !cover_s8 && !cover_s9
  in
  Printf.printf
    "build_fails=%d dispatch_fails=%d bridge_fails=%d\n\
     coverage: S1(collision-bridge)=%b S1(dispatch-tag0)=%b S1(dispatch-tag1)=%b \
     S2(deep-nest)=%b S3(empty-list)=%b\n\
     S4(large-list)=%b S5(mixed-list)=%b S6(z-boundary-bridge)=%b S6(z-boundary-dispatch)=%b \
     S7(wrong-tag->default)=%b S8(non-tag->default)=%b S9(fuzz)=%b\n"
    !build_fails !dispatch_fails !bridge_fails !cover_s1 !cover_s1_tag0 !cover_s1_tag1 !cover_s2
    !cover_s3 !cover_s4 !cover_s5 !cover_s6 !cover_s6_dispatch !cover_s7 !cover_s8 !cover_s9;
  if !build_fails = 0 && !dispatch_fails = 0 && !bridge_fails = 0 && cov_ok then
    print_endline
      "STRUCTVAL DIFFERENTIAL OK: reference == fast (tag_build + tag_dispatch) + bridge \
       round-trip; coverage asserted"
  else begin
    if not cov_ok then
      print_endline "STRUCTVAL COVERAGE GAP: a required class (S1-S9) was never exercised";
    exit 1
  end
