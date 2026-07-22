(** Differential test for VPrim primitives (IR v2 R3, adr-0009-vprim-registry).

    Exercises [sample_parse] (PParseInt64 + PAddChecked + PPrintInt pipeline) across
    adversarially-biased input contexts, comparing the reference interpreter against the
    generated direct-style code over [Rval.t].

    Grammar-violation classes tested (each must be covered; coverage is ASSERTED):
      G1  exact "0"                    -> DSome (DInt 1); "1" printed as "1"
      G2  exact "9223372036854775807"  -> int64_max; PAddChecked -> overflow (OVF)
      G3  "9223372036854775808"        -> overflow on parse (ERR; exceeds int64_max)
      G4  "-9223372036854775808"       -> int64_min; add 1 -> within range
      G5  "-9223372036854775809"       -> out of range (ERR)
      G6  "0123"                       -> leading-zero violation (ERR)
      G7  " 5"                         -> leading-space violation (ERR)
      G8  "+5"                         -> leading-plus violation (ERR)
      G9  ""                           -> empty input (ERR)
      G10 "-0"                         -> minus-zero, not canonical (ERR)
      G11 "1e3"                        -> non-digit in body (ERR)
      G12 "9223372036854775807..."     -> 20+ digit number exceeding int64 (ERR)
      G13 binary junk (non-digit bytes)-> (ERR)
      G14 valid positive decimal       -> success + increment + print
      G15 valid negative decimal       -> success + increment + print
      G16 "-"                          -> bare minus (ERR)

    Seeds are logged; every counterexample is printed with its seed for corpus replay.
    Reference == fast byte-identical is asserted for every tested input.

    R6 (adr-0012-list-elimination) adds direct apply_prim-vs-realizer rounds for
    PMulChecked (int64 boundaries incl. the asymmetric -1 * int64_min = 2^63 overflow)
    and PListLen/PListNth (index bias -1 / 0 / len-1 / len / huge-Z beyond native int;
    mixed-shape and empty lists; shape mismatches).

    R9 (adr-0013 milestone; adr-0009 discipline) adds PDivFloor direct rounds with
    boundary bias: NEGATIVE dividends — floor and truncation DIFFER there, and both
    sides must say (-7)/2 = -4 (the realizer uses Z.fdiv; zarith's Z.div truncates);
    divisor 0 -> None with no exception; int64 boundaries incl. int64_min / -1 -> None (range);
    shape mismatches.

    R12 (adr-0009 discipline) adds PLowerBytes/PUpperBytes: ALL 256 single bytes are
    asserted EXHAUSTIVELY (ref == fast == the spec value: 65-90 +32 for lower, 97-122
    -32 for upper, every other byte fixed — incl. > 127); random mixed strings; empty;
    NUL-embedded; shape mismatches; plus [sample_ci_dispatch] (Env token ->
    PLowerBytes -> Match "nx"/"xx"/default) through the reference-vs-generated
    pipeline with per-branch coverage (C1-C5) asserted.

    R13 (adr-0009 discipline) adds PListSnoc direct rounds: random mixed-shape
    lists x mixed-shape elements (incl. nested List/Tag), plus fixed VALUE-asserted
    cases (not just ref==fast) pinning the ORDER — element at the END, prefix
    untouched: empty list, large (1200-element) list, nested-list and tagged
    elements, shape mismatches -> None. The collecting-fold sample itself
    ([sample_fold_collect]) runs through the reference-vs-generated pipeline with
    fuzzed stores in diff_fold.ml (M1-M7). *)

module E   = Ref_extracted.EffIR
module D   = Ref_extracted.Datatypes
module S   = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

(* --- reference side -------------------------------------------------------- *)

(** Run [sample_parse] with a Bytes context; extract the outcome. *)
let ref_outcome (ctx_bytes : bytes) : Rkv.Rval.t =
  let coq_ctx = E.DBytes (Coqconv.bytes_to_ascii_list ctx_bytes) in
  match E.run_top coq_ctx (Coqconv.coqz_of_z Z.zero) S.sample_parse with
  | D.Coq_pair (E.ORet v, _) -> Coqconv.rval_of_dval v
  | D.Coq_pair (E.OErr e, _) ->
      failwith ("diff_prims ref error: " ^ Rkv.Rval.to_string (Coqconv.rval_of_dval e))

(* --- fast side ------------------------------------------------------------- *)

(** Run the generated [sample_parse] under the Env handler (no KV needed). *)
let fast_outcome (ctx_bytes : bytes) : Rkv.Rval.t =
  let result = ref Rkv.Rval.None in
  Rkv.Env.run (Rkv.Rval.Bytes ctx_bytes) (fun () ->
    result := Gen.sample_parse ());
  !result

(* --- R12 pipeline: sample_ci_dispatch reference vs generated ---------------- *)

(** Run [sample_ci_dispatch] with a Bytes context on the reference interpreter. *)
let ref_ci_outcome (ctx_bytes : bytes) : Rkv.Rval.t =
  let coq_ctx = E.DBytes (Coqconv.bytes_to_ascii_list ctx_bytes) in
  match E.run_top coq_ctx (Coqconv.coqz_of_z Z.zero) S.sample_ci_dispatch with
  | D.Coq_pair (E.ORet v, _) -> Coqconv.rval_of_dval v
  | D.Coq_pair (E.OErr e, _) ->
      failwith ("diff_prims ci ref error: " ^ Rkv.Rval.to_string (Coqconv.rval_of_dval e))

(** Run the generated [sample_ci_dispatch] under the Env handler (no KV needed). *)
let fast_ci_outcome (ctx_bytes : bytes) : Rkv.Rval.t =
  let result = ref Rkv.Rval.None in
  Rkv.Env.run (Rkv.Rval.Bytes ctx_bytes) (fun () ->
    result := Gen.sample_ci_dispatch ());
  !result

(* --- expected outcomes for specific inputs --------------------------------- *)

let err_bytes = Bytes.of_string "ERR"
let ovf_bytes = Bytes.of_string "OVF"

(** For a valid, non-overflow decimal string [s], the expected output is the decimal
    of (parse(s) + 1). We compute this via the reference oracle. *)

(* --- seeded generator ------------------------------------------------------ *)

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260710
let rng = Random.State.make [| seed |]

let rand_digit () =
  Char.chr (Char.code '0' + Random.State.int rng 10)

let gen_valid_pos () : bytes =
  (* nonzero leading digit, then more digits *)
  let first = Char.chr (Char.code '1' + Random.State.int rng 9) in
  let n = Random.State.int rng 10 in
  let buf = Buffer.create (n + 1) in
  Buffer.add_char buf first;
  for _ = 1 to n do Buffer.add_char buf (rand_digit ()) done;
  Buffer.contents buf |> Bytes.of_string

let gen_valid_neg () : bytes =
  let pos = gen_valid_pos () in
  let s = "-" ^ Bytes.to_string pos in
  Bytes.of_string s

(** Bias generator toward grammar-violation and boundary classes. *)
let gen_input () : bytes =
  match Random.State.int rng 32 with
  | 0  -> Bytes.of_string "0"                              (* G1: zero *)
  | 1  -> Bytes.of_string "9223372036854775807"            (* G2: int64_max (overflow on add) *)
  | 2  -> Bytes.of_string "9223372036854775808"            (* G3: int64_max+1 (parse overflow) *)
  | 3  -> Bytes.of_string "-9223372036854775808"           (* G4: int64_min *)
  | 4  -> Bytes.of_string "-9223372036854775809"           (* G5: int64_min-1 *)
  | 5  -> Bytes.of_string "0123"                           (* G6: leading zero *)
  | 6  -> Bytes.of_string " 5"                             (* G7: leading space *)
  | 7  -> Bytes.of_string "+5"                             (* G8: leading plus *)
  | 8  -> Bytes.empty                                      (* G9: empty *)
  | 9  -> Bytes.of_string "-0"                             (* G10: minus zero *)
  | 10 -> Bytes.of_string "1e3"                            (* G11: sci notation *)
  | 11 -> Bytes.of_string "99999999999999999999"           (* G12: 20-digit overflow *)
  | 12 ->                                                   (* G13: binary junk *)
      Bytes.init (1 + Random.State.int rng 8)
        (fun _ -> Char.chr (Random.State.int rng 48))  (* below '0' *)
  | 13 -> Bytes.of_string "-"                              (* G16: bare minus *)
  | 14 | 15 -> gen_valid_pos ()                            (* G14: valid positive *)
  | 16 | 17 -> gen_valid_neg ()                            (* G15: valid negative *)
  | _ ->
      (* Random mix: could be valid or invalid *)
      let n = Random.State.int rng 12 in
      Bytes.init n (fun _ ->
        let c = Random.State.int rng 128 in
        Char.chr c)

(* --- coverage tracking ----------------------------------------------------- *)

let cover_g1  = ref false   (* "0" *)
let cover_g2  = ref false   (* int64_max -> overflow on add *)
let cover_g3  = ref false   (* parse overflow high *)
let cover_g4  = ref false   (* int64_min *)
let cover_g5  = ref false   (* parse overflow low *)
let cover_g6  = ref false   (* leading zero "0123" *)
let cover_g7  = ref false   (* leading space " 5" *)
let cover_g8  = ref false   (* leading plus "+5" *)
let cover_g9  = ref false   (* empty "" *)
let cover_g10 = ref false   (* minus zero "-0" *)
let cover_g11 = ref false   (* sci notation "1e3" *)
let cover_g12 = ref false   (* 20+ digits *)
let cover_g13 = ref false   (* binary junk *)
let cover_g14 = ref false   (* valid positive (success) *)
let cover_g15 = ref false   (* valid negative (success) *)
let cover_g16 = ref false   (* bare minus "-" *)

let note_input (b : bytes) (r : Rkv.Rval.t) =
  let s = Bytes.to_string b in
  if s = "0" then cover_g1 := true;
  if s = "9223372036854775807" then cover_g2 := true;
  if s = "9223372036854775808" then cover_g3 := true;
  if s = "-9223372036854775808" then cover_g4 := true;
  if s = "-9223372036854775809" then cover_g5 := true;
  if s = "0123" then cover_g6 := true;
  if s = " 5" then cover_g7 := true;
  if s = "+5" then cover_g8 := true;
  if Bytes.length b = 0 then cover_g9 := true;
  if s = "-0" then cover_g10 := true;
  if s = "1e3" then cover_g11 := true;
  if String.length s >= 20 && s.[0] <> '-' then cover_g12 := true;
  if Bytes.length b > 0 then begin
    let all_below_digit = Bytes.for_all (fun c -> Char.code c < 45 || Char.code c > 57) b in
    if all_below_digit then cover_g13 := true
  end;
  if s = "-" then cover_g16 := true;
  (* G14: valid positive -> success (Some result, not ERR or OVF) *)
  (match r with
   | Rkv.Rval.Bytes ob when not (Bytes.equal ob err_bytes) && not (Bytes.equal ob ovf_bytes) ->
       if Bytes.length b > 0 && Bytes.get b 0 <> '-' then cover_g14 := true;
       if Bytes.length b > 1 && Bytes.get b 0 = '-' then cover_g15 := true
   | _ -> ())

(* --- direct per-prim differential ------------------------------------------ *)
(* [sample_parse] only reaches PParseInt64/PAddChecked/PPrintInt. The manifest claims
   diff_prims validates EVERY realizer, so the remaining prims (and the three above, at
   the raw apply_prim level) are compared here directly: extracted [apply_prim] reference
   vs the [Prims.*] realizer, over boundary-biased inputs. *)

let coq_list_of (l : 'a list) : 'a D.list =
  List.fold_right (fun x acc -> D.Coq_cons (x, acc)) l D.Coq_nil

let ref_prim (p : E.prim) (args : Rkv.Rval.t list) : Rkv.Rval.t =
  Coqconv.rval_of_dval
    (E.apply_prim p (coq_list_of (List.map Coqconv.dval_of_rval args)))

let int64_max = Z.of_string "9223372036854775807"
let int64_min = Z.of_string "-9223372036854775808"

(** Boundary-biased int64-range Z generator. *)
let gen_z () : Z.t =
  match Random.State.int rng 10 with
  | 0 -> int64_max
  | 1 -> int64_min
  | 2 -> Z.zero
  | 3 -> Z.sub int64_max (Z.of_int (Random.State.int rng 3))
  | 4 -> Z.add int64_min (Z.of_int (Random.State.int rng 3))
  | 5 -> Z.of_string "4611686018427387904"   (* 2^62 *)
  | _ -> Z.of_int (Random.State.int rng 2001 - 1000)

(** Small byte strings incl. empty and NUL-carrying. *)
let gen_bytes () : bytes =
  match Random.State.int rng 6 with
  | 0 -> Bytes.empty
  | 1 -> Bytes.of_string "\x00"
  | _ -> Bytes.init (Random.State.int rng 12)
           (fun _ -> Char.chr (Random.State.int rng 256))

(** Mixed-shape list values for the R6 list prims (incl. empty). *)
let gen_list_val () : Rkv.Rval.t =
  let n = Random.State.int rng 7 in
  Rkv.Rval.List
    (List.init n (fun i ->
         match Random.State.int rng 4 with
         | 0 -> Rkv.Rval.Int (Z.of_int i)
         | 1 -> Rkv.Rval.Bytes (gen_bytes ())
         | 2 -> Rkv.Rval.Unit
         | _ -> Rkv.Rval.Pair (Rkv.Rval.Int (Z.of_int i), Rkv.Rval.Bool true)))

let prim_fails = ref 0

let check_prim (name : string) (p : E.prim) (impl : Rkv.Rval.t list -> Rkv.Rval.t)
    (args : Rkv.Rval.t list) =
  let r = ref_prim p args in
  let f = impl args in
  if not (Rkv.Rval.equal r f) then begin
    incr prim_fails;
    Printf.printf "PRIM MISMATCH (RSEED=%d) %s args=[%s]\n  ref=%s\n  fast=%s\n"
      seed name
      (String.concat "; " (List.map Rkv.Rval.to_string args))
      (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
  end

let app2 g = function [a; b] -> g a b | _ -> assert false
let app3 g = function [a; b; c] -> g a b c | _ -> assert false
let app1 g = function [a] -> g a | _ -> assert false

let direct_prim_pass () =
  for _ = 1 to 2000 do
    let za = gen_z () and zb = gen_z () in
    let ia = Rkv.Rval.Int za and ib = Rkv.Rval.Int zb in
    let ba = Rkv.Rval.Bytes (gen_bytes ()) and bb = Rkv.Rval.Bytes (gen_bytes ()) in
    check_prim "add_checked" E.PAddChecked (app2 Rkv.Prims.prim_add_checked) [ia; ib];
    check_prim "sub_checked" E.PSubChecked (app2 Rkv.Prims.prim_sub_checked) [ia; ib];
    check_prim "cmp_int"     E.PCmpInt     (app2 Rkv.Prims.prim_cmp_int)     [ia; ib];
    check_prim "eq_bytes"    E.PEqBytes    (app2 Rkv.Prims.prim_eq_bytes)    [ba; bb];
    (* eq_bytes biased-equal case (uniform pairs rarely collide) *)
    check_prim "eq_bytes"    E.PEqBytes    (app2 Rkv.Prims.prim_eq_bytes)    [ba; ba];
    check_prim "bytes_len"   E.PBytesLen   (app1 Rkv.Prims.prim_bytes_len)   [ba];
    check_prim "bytes_concat" E.PBytesConcat (app2 Rkv.Prims.prim_bytes_concat) [ba; bb];
    (* bytes_sub: offsets/lens biased to slice edges (-1, 0, len, len+1) *)
    let blen = (match ba with Rkv.Rval.Bytes b -> Bytes.length b | _ -> 0) in
    let edge () =
      match Random.State.int rng 6 with
      | 0 -> Z.of_int (-1)
      | 1 -> Z.zero
      | 2 -> Z.of_int blen
      | 3 -> Z.of_int (blen + 1)
      | _ -> Z.of_int (Random.State.int rng (blen + 2))
    in
    check_prim "bytes_sub" E.PBytesSub (app3 Rkv.Prims.prim_bytes_sub)
      [ba; Rkv.Rval.Int (edge ()); Rkv.Rval.Int (edge ())];
    check_prim "parse_int64" E.PParseInt64 (app1 Rkv.Prims.prim_parse_int64)
      [Rkv.Rval.Bytes (gen_input ())];
    check_prim "print_int" E.PPrintInt (app1 Rkv.Prims.prim_print_int) [ia];
    (* print/parse composed at the realizer level: canonical round-trip *)
    (match Rkv.Prims.prim_print_int ia with
     | Rkv.Rval.Some (Rkv.Rval.Bytes s) ->
         check_prim "parse_int64" E.PParseInt64 (app1 Rkv.Prims.prim_parse_int64)
           [Rkv.Rval.Bytes s]
     | _ -> ());
    (* R6 prims (adr-0012): mul boundaries + list len/nth with index bias *)
    check_prim "mul_checked" E.PMulChecked (app2 Rkv.Prims.prim_mul_checked) [ia; ib];
    let lv = gen_list_val () in
    let llen = (match lv with Rkv.Rval.List l -> List.length l | _ -> 0) in
    check_prim "list_len" E.PListLen (app1 Rkv.Prims.prim_list_len) [lv];
    (* index bias: -1 / 0 / len-1 / len / huge-Z / random (adr-0012 §implementers) *)
    let idx =
      match Random.State.int rng 7 with
      | 0 -> Z.of_int (-1)
      | 1 -> Z.zero
      | 2 -> Z.of_int (llen - 1)
      | 3 -> Z.of_int llen
      | 4 -> Z.of_string "1180591620717411303424"  (* 2^70: beyond native int *)
      | 5 -> Z.neg (Z.of_string "1180591620717411303424")
      | _ -> Z.of_int (Random.State.int rng (llen + 2))
    in
    check_prim "list_nth" E.PListNth (app2 Rkv.Prims.prim_list_nth)
      [lv; Rkv.Rval.Int idx];
    (* R9 prim: floor division with a divisor biased to 0 / ±1 / ±2 (0 exercises the
       no-exception None path; ±1/±2 with negative random dividends exercise the
       floor-vs-truncation boundary on every round) *)
    let db =
      match Random.State.int rng 6 with
      | 0 -> Z.zero
      | 1 -> Z.one
      | 2 -> Z.minus_one
      | 3 -> Z.of_int 2
      | 4 -> Z.of_int (-2)
      | _ -> zb
    in
    check_prim "div_floor" E.PDivFloor (app2 Rkv.Prims.prim_div_floor)
      [ia; Rkv.Rval.Int db];
    (* R12 prims: random mixed strings (gen_bytes is full-range 0-255, incl. empty and
       NUL-carrying) through both case folds *)
    check_prim "lower_bytes" E.PLowerBytes (app1 Rkv.Prims.prim_lower_bytes) [ba];
    check_prim "upper_bytes" E.PUpperBytes (app1 Rkv.Prims.prim_upper_bytes) [bb];
    (* R13 prim: list snoc — mixed-shape lists x mixed-shape elements, incl. a nested
       List and a Tag element (the reply-slot shape) *)
    let sv =
      match Random.State.int rng 5 with
      | 0 -> ia
      | 1 -> Rkv.Rval.Bytes (gen_bytes ())
      | 2 -> Rkv.Rval.Tag (Z.one, ib)
      | 3 -> gen_list_val ()   (* nested list element *)
      | _ -> Rkv.Rval.Unit
    in
    check_prim "list_snoc" E.PListSnoc (app2 Rkv.Prims.prim_list_snoc) [lv; sv];
    (* C4 rider prim (adr-0018): find_sub over random hay/needle byte pairs *)
    check_prim "find_sub" E.PFindSub (app2 Rkv.Prims.prim_find_sub)
      [Rkv.Rval.Bytes (gen_bytes ()); Rkv.Rval.Bytes (gen_bytes ())]
  done;
  (* Fixed adversarial cases *)
  let huge = Rkv.Rval.Int (Z.of_string "1180591620717411303424") (* 2^70: must be DNone, not Z.Overflow *) in
  check_prim "bytes_sub" E.PBytesSub (app3 Rkv.Prims.prim_bytes_sub)
    [Rkv.Rval.Bytes (Bytes.of_string "hello"); huge; Rkv.Rval.Int Z.one];
  check_prim "bytes_sub" E.PBytesSub (app3 Rkv.Prims.prim_bytes_sub)
    [Rkv.Rval.Bytes (Bytes.of_string "hello"); Rkv.Rval.Int Z.one; huge];
  check_prim "print_int" E.PPrintInt (app1 Rkv.Prims.prim_print_int)
    [huge  (* out of int64 range: DNone *)];
  check_prim "add_checked" E.PAddChecked (app2 Rkv.Prims.prim_add_checked)
    [Rkv.Rval.Int int64_max; Rkv.Rval.Int Z.one];
  check_prim "sub_checked" E.PSubChecked (app2 Rkv.Prims.prim_sub_checked)
    [Rkv.Rval.Int int64_min; Rkv.Rval.Int Z.one];
  (* R6 fixed adversarial cases: int64 multiplication boundaries — incl. the ASYMMETRIC
     -1 * int64_min = 2^63 overflow (in range for |min| but not for max) *)
  check_prim "mul_checked" E.PMulChecked (app2 Rkv.Prims.prim_mul_checked)
    [Rkv.Rval.Int int64_max; Rkv.Rval.Int (Z.of_int 2)];
  check_prim "mul_checked" E.PMulChecked (app2 Rkv.Prims.prim_mul_checked)
    [Rkv.Rval.Int (Z.of_int (-1)); Rkv.Rval.Int int64_min];
  check_prim "mul_checked" E.PMulChecked (app2 Rkv.Prims.prim_mul_checked)
    [Rkv.Rval.Int int64_min; Rkv.Rval.Int (Z.of_int (-1))];
  check_prim "mul_checked" E.PMulChecked (app2 Rkv.Prims.prim_mul_checked)
    [Rkv.Rval.Int int64_max; Rkv.Rval.Int Z.one];
  check_prim "mul_checked" E.PMulChecked (app2 Rkv.Prims.prim_mul_checked)
    [Rkv.Rval.Int int64_min; Rkv.Rval.Int Z.one];
  check_prim "mul_checked" E.PMulChecked (app2 Rkv.Prims.prim_mul_checked)
    [Rkv.Rval.Int (Z.of_int 1000); Rkv.Rval.Int (Z.of_string "9007199254740")];
  (* R6 fixed adversarial cases: list_nth on huge Z indices (must be DNone, never
     Z.Overflow — the prim_bytes_sub lesson) and exact len-1/len edges *)
  let l3 = Rkv.Rval.List [Rkv.Rval.Int Z.zero; Rkv.Rval.Unit; Rkv.Rval.Bytes Bytes.empty] in
  check_prim "list_nth" E.PListNth (app2 Rkv.Prims.prim_list_nth) [l3; huge];
  check_prim "list_nth" E.PListNth (app2 Rkv.Prims.prim_list_nth)
    [l3; Rkv.Rval.Int (Z.of_int (-1))];
  check_prim "list_nth" E.PListNth (app2 Rkv.Prims.prim_list_nth)
    [l3; Rkv.Rval.Int (Z.of_int 2)];
  check_prim "list_nth" E.PListNth (app2 Rkv.Prims.prim_list_nth)
    [l3; Rkv.Rval.Int (Z.of_int 3)];
  check_prim "list_len" E.PListLen (app1 Rkv.Prims.prim_list_len) [Rkv.Rval.List []];
  (* shape mismatches: both sides must agree on DNone *)
  check_prim "add_checked" E.PAddChecked (app2 Rkv.Prims.prim_add_checked)
    [Rkv.Rval.Bytes (Bytes.of_string "1"); Rkv.Rval.Int Z.one];
  check_prim "bytes_len" E.PBytesLen (app1 Rkv.Prims.prim_bytes_len) [Rkv.Rval.Int Z.zero];
  check_prim "eq_bytes" E.PEqBytes (app2 Rkv.Prims.prim_eq_bytes)
    [Rkv.Rval.Unit; Rkv.Rval.Bytes Bytes.empty];
  check_prim "mul_checked" E.PMulChecked (app2 Rkv.Prims.prim_mul_checked)
    [Rkv.Rval.Bytes (Bytes.of_string "2"); Rkv.Rval.Int Z.one];
  check_prim "list_len" E.PListLen (app1 Rkv.Prims.prim_list_len) [Rkv.Rval.Int Z.zero];
  check_prim "list_nth" E.PListNth (app2 Rkv.Prims.prim_list_nth)
    [Rkv.Rval.Int Z.zero; Rkv.Rval.Int Z.zero];
  check_prim "list_nth" E.PListNth (app2 Rkv.Prims.prim_list_nth)
    [l3; Rkv.Rval.Bytes (Bytes.of_string "0")];
  (* R9 fixed adversarial cases: PDivFloor. The VALUE is asserted (not just ref==fast)
     on the floor/truncation discriminator: (-7)/2 = -4 on BOTH sides. *)
  let zi n = Rkv.Rval.Int (Z.of_int n) in
  let assert_div a b expect what =
    let r = ref_prim E.PDivFloor [a; b] and f = Rkv.Prims.prim_div_floor a b in
    if not (Rkv.Rval.equal r expect && Rkv.Rval.equal f expect) then begin
      incr prim_fails;
      Printf.printf
        "DIV_FLOOR VALUE FAIL (RSEED=%d) %s: expected %s, ref=%s fast=%s\n"
        seed what (Rkv.Rval.to_string expect)
        (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
    end
  in
  assert_div (zi (-7)) (zi 2) (Rkv.Rval.Some (zi (-4))) "(-7)/2 floor (trunc would be -3)";
  assert_div (zi 7) (zi (-2)) (Rkv.Rval.Some (zi (-4))) "7/(-2) floor";
  assert_div (zi (-7)) (zi (-2)) (Rkv.Rval.Some (zi 3)) "(-7)/(-2) floor";
  assert_div (zi 7) (zi 2) (Rkv.Rval.Some (zi 3)) "7/2";
  assert_div (zi 5) (zi 0) Rkv.Rval.None "x/0 -> None (no exception)";
  assert_div (zi 0) (zi 0) Rkv.Rval.None "0/0 -> None";
  assert_div (Rkv.Rval.Int int64_min) (zi (-1)) Rkv.Rval.None
    "int64_min / -1 overflows int64 -> None (range-checked)";
  assert_div (Rkv.Rval.Int int64_min) (zi 1)
    (Rkv.Rval.Some (Rkv.Rval.Int int64_min)) "int64_min / 1";
  assert_div (Rkv.Rval.Int int64_max) (zi (-1))
    (Rkv.Rval.Some (Rkv.Rval.Int (Z.neg int64_max))) "int64_max / -1";
  assert_div (Rkv.Rval.Int int64_max) (Rkv.Rval.Int int64_max)
    (Rkv.Rval.Some (zi 1)) "max/max";
  (* shape mismatches: both sides must agree on None *)
  check_prim "div_floor" E.PDivFloor (app2 Rkv.Prims.prim_div_floor)
    [Rkv.Rval.Bytes (Bytes.of_string "7"); zi 2];
  check_prim "div_floor" E.PDivFloor (app2 Rkv.Prims.prim_div_floor)
    [zi 7; Rkv.Rval.Unit];
  (* R12 fixed adversarial cases: PLowerBytes/PUpperBytes.
     EXHAUSTIVE single-byte pass: for EVERY byte 0-255, the VALUE is asserted (not just
     ref==fast) against the spec — 65-90 shifted +32 for lower, 97-122 shifted -32 for
     upper, EVERY other byte fixed (digits, punctuation, NUL, and >127: pure ASCII fold,
     no latin-1/UTF-8 folding). *)
  let assert_fold name p impl expected_map what b =
    let arg = Rkv.Rval.Bytes b in
    let expect = Rkv.Rval.Bytes (Bytes.map expected_map b) in
    let r = ref_prim p [arg] and f = impl arg in
    if not (Rkv.Rval.equal r expect && Rkv.Rval.equal f expect) then begin
      incr prim_fails;
      Printf.printf
        "CASE_FOLD VALUE FAIL (RSEED=%d) %s %s: input=%s expected %s, ref=%s fast=%s\n"
        seed name what (Rkv.Rval.to_string arg) (Rkv.Rval.to_string expect)
        (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
    end
  in
  let spec_lower c =
    let n = Char.code c in if n >= 65 && n <= 90 then Char.chr (n + 32) else c in
  let spec_upper c =
    let n = Char.code c in if n >= 97 && n <= 122 then Char.chr (n - 32) else c in
  let assert_lower = assert_fold "lower_bytes" E.PLowerBytes
      Rkv.Prims.prim_lower_bytes spec_lower in
  let assert_upper = assert_fold "upper_bytes" E.PUpperBytes
      Rkv.Prims.prim_upper_bytes spec_upper in
  for i = 0 to 255 do
    let b = Bytes.make 1 (Char.chr i) in
    assert_lower (Printf.sprintf "byte 0x%02x" i) b;
    assert_upper (Printf.sprintf "byte 0x%02x" i) b
  done;
  (* empty; NUL-embedded (letters AROUND the NUL must still fold); driver tokens *)
  assert_lower "empty" Bytes.empty;
  assert_upper "empty" Bytes.empty;
  assert_lower "NUL-embedded" (Bytes.of_string "Ab\x00Cd\xff-9Z");
  assert_upper "NUL-embedded" (Bytes.of_string "Ab\x00Cd\xff-9z");
  assert_lower "driver token" (Bytes.of_string "KeepTtl");
  assert_upper "driver token" (Bytes.of_string "KeepTtl");
  (* the realizer must NOT mutate its input (fresh Bytes.map buffer) *)
  let original = Bytes.of_string "MiXeD" in
  let copy = Bytes.copy original in
  ignore (Rkv.Prims.prim_lower_bytes (Rkv.Rval.Bytes original));
  ignore (Rkv.Prims.prim_upper_bytes (Rkv.Rval.Bytes original));
  if not (Bytes.equal original copy) then begin
    incr prim_fails;
    Printf.printf "CASE_FOLD MUTATION FAIL (RSEED=%d): realizer mutated its input\n" seed
  end;
  (* shape mismatches: both sides must agree on None *)
  check_prim "lower_bytes" E.PLowerBytes (app1 Rkv.Prims.prim_lower_bytes)
    [Rkv.Rval.Int (Z.of_int 65)];
  check_prim "upper_bytes" E.PUpperBytes (app1 Rkv.Prims.prim_upper_bytes)
    [Rkv.Rval.Unit];
  check_prim "lower_bytes" E.PLowerBytes (app1 Rkv.Prims.prim_lower_bytes)
    [Rkv.Rval.List [Rkv.Rval.Bytes (Bytes.of_string "NX")]];
  (* R13 fixed adversarial cases: PListSnoc. The VALUE is asserted (not just
     ref==fast) so the ORDER is pinned on both sides — the element lands at the END,
     the prefix is untouched (a prepend realizer must fail these). *)
  let assert_snoc l v expect what =
    let r = ref_prim E.PListSnoc [l; v] and f = Rkv.Prims.prim_list_snoc l v in
    if not (Rkv.Rval.equal r expect && Rkv.Rval.equal f expect) then begin
      incr prim_fails;
      Printf.printf
        "LIST_SNOC VALUE FAIL (RSEED=%d) %s: expected %s, ref=%s fast=%s\n"
        seed what (Rkv.Rval.to_string expect)
        (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
    end
  in
  (* empty list: the element becomes the single slot *)
  assert_snoc (Rkv.Rval.List []) (zi 7) (Rkv.Rval.List [zi 7]) "snoc onto empty";
  (* order: element at the END, not the front *)
  assert_snoc (Rkv.Rval.List [zi 1; zi 2]) (zi 3)
    (Rkv.Rval.List [zi 1; zi 2; zi 3]) "snoc order (end, not front)";
  (* nested shapes: a List element is ONE slot (never concatenated); Tag slots nest *)
  assert_snoc (Rkv.Rval.List [zi 1]) (Rkv.Rval.List [zi 2; zi 3])
    (Rkv.Rval.List [zi 1; Rkv.Rval.List [zi 2; zi 3]]) "nested list element";
  assert_snoc (Rkv.Rval.List [Rkv.Rval.Tag (Z.zero, Rkv.Rval.Unit)])
    (Rkv.Rval.Tag (Z.one, Rkv.Rval.Bytes (Bytes.of_string "v")))
    (Rkv.Rval.List [Rkv.Rval.Tag (Z.zero, Rkv.Rval.Unit);
                    Rkv.Rval.Tag (Z.one, Rkv.Rval.Bytes (Bytes.of_string "v"))])
    "tagged element";
  (* LARGE (1000+): the whole 1200-element prefix survives IN ORDER *)
  let big = List.init 1200 (fun i -> Rkv.Rval.Int (Z.of_int i)) in
  assert_snoc (Rkv.Rval.List big) (zi 1200)
    (Rkv.Rval.List (big @ [zi 1200])) "large 1200-element snoc";
  (* shape mismatches: both sides must agree on None *)
  check_prim "list_snoc" E.PListSnoc (app2 Rkv.Prims.prim_list_snoc) [zi 0; zi 1];
  check_prim "list_snoc" E.PListSnoc (app2 Rkv.Prims.prim_list_snoc)
    [Rkv.Rval.Bytes (Bytes.of_string "k"); zi 1];
  (* C4 rider prim (adr-0018): PFindSub fixed adversarial cases — VALUE asserted so
     the FIRST-match rule and boundary indices are pinned on both sides. *)
  let bsv s = Rkv.Rval.Bytes (Bytes.of_string s) in
  let assert_find h n expect what =
    let r = ref_prim E.PFindSub [bsv h; bsv n]
    and f = Rkv.Prims.prim_find_sub (bsv h) (bsv n) in
    if not (Rkv.Rval.equal r expect && Rkv.Rval.equal f expect) then begin
      incr prim_fails;
      Printf.printf "FIND_SUB VALUE FAIL (RSEED=%d) %s: expected %s, ref=%s fast=%s\n"
        seed what (Rkv.Rval.to_string expect)
        (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
    end
  in
  let found i = Rkv.Rval.Some (zi i) in
  assert_find "hello" "he" (found 0) "needle at start";
  assert_find "hello" "lo" (found 3) "needle at end";
  assert_find "hello" "x" Rkv.Rval.None "absent";
  assert_find "hello" "" (found 0) "empty needle -> 0";
  assert_find "" "" (found 0) "empty in empty -> 0";
  assert_find "" "a" Rkv.Rval.None "nonempty in empty";
  assert_find "hello" "hello" (found 0) "needle == hay";
  assert_find "hello" "hellox" Rkv.Rval.None "needle longer than hay";
  assert_find "aaaa" "aa" (found 0) "overlapping candidates: FIRST wins";
  assert_find "abcabc" "cab" (found 2) "interior straddling occurrence";
  assert_find "a\x00b" "\x00" (found 1) "NUL needle";
  (* the request-line shape the C4 server parses *)
  assert_find "GET /p HTTP/1.0\r\nHost: x\r\n\r\n" "\r\n" (found 15) "first CRLF";
  check_prim "find_sub" E.PFindSub (app2 Rkv.Prims.prim_find_sub) [zi 0; bsv "x"];
  check_prim "find_sub" E.PFindSub (app2 Rkv.Prims.prim_find_sub) [bsv "x"; Rkv.Rval.Unit]

(* --- R12 pipeline pass: sample_ci_dispatch ---------------------------------- *)
(* Case-insensitive dispatch through the FULL reference-vs-generated pipeline: the
   token case-folds via PLowerBytes, then matches lowercase literals — so every
   capitalization of "nx"/"xx" must take its branch, and everything else (incl. empty,
   NUL, high bytes) the default. Coverage classes (asserted):
     C1  "nx" in some NON-lowercase capitalization -> 1 (the prim is load-bearing)
     C2  "xx" in some NON-lowercase capitalization -> 2
     C3  other token -> default 0
     C4  empty bytes -> default 0
     C5  bytes > 127 -> default 0 (pure ASCII fold posture crosses the pipeline) *)

let ci_fails = ref 0
let cover_c1 = ref false
let cover_c2 = ref false
let cover_c3 = ref false
let cover_c4 = ref false
let cover_c5 = ref false

let gen_ci_token () : bytes =
  let mix_case s =
    Bytes.of_string
      (String.map (fun c -> if Random.State.bool rng then Char.uppercase_ascii c else c) s)
  in
  match Random.State.int rng 12 with
  | 0 | 1 -> mix_case "nx"
  | 2 | 3 -> mix_case "xx"
  | 4     -> mix_case "keepttl"
  | 5     -> Bytes.empty
  | 6     -> Bytes.of_string "\x00nx"                       (* NUL prefix: default *)
  | 7     -> Bytes.init (1 + Random.State.int rng 6)
               (fun _ -> Char.chr (0x80 + Random.State.int rng 0x80))  (* high bytes *)
  | _     -> Bytes.init (Random.State.int rng 6)
               (fun _ -> Char.chr (Random.State.int rng 256))

let ci_dispatch_pass () =
  let lower_of b =
    Bytes.map (fun c ->
        let n = Char.code c in
        if n >= 65 && n <= 90 then Char.chr (n + 32) else c) b
  in
  for _ = 1 to 3000 do
    let tok = gen_ci_token () in
    let r = ref_ci_outcome tok and f = fast_ci_outcome tok in
    if not (Rkv.Rval.equal r f) then begin
      incr ci_fails;
      Printf.printf "CI-DISPATCH MISMATCH (RSEED=%d) token=%s\n  ref=%s\n  fast=%s\n"
        seed (Rkv.Rval.to_string (Rkv.Rval.Bytes tok))
        (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
    end else begin
      (* validate the expected branch AND record coverage *)
      let folded = Bytes.to_string (lower_of tok) in
      let expect =
        if folded = "nx" then 1 else if folded = "xx" then 2 else 0 in
      if not (Rkv.Rval.equal r (Rkv.Rval.Int (Z.of_int expect))) then begin
        incr ci_fails;
        Printf.printf "CI-DISPATCH BRANCH FAIL (RSEED=%d) token=%s expected %d got %s\n"
          seed (Rkv.Rval.to_string (Rkv.Rval.Bytes tok)) expect (Rkv.Rval.to_string r)
      end;
      let raw = Bytes.to_string tok in
      if folded = "nx" && raw <> "nx" then cover_c1 := true;
      if folded = "xx" && raw <> "xx" then cover_c2 := true;
      if expect = 0 && Bytes.length tok > 0 then cover_c3 := true;
      if Bytes.length tok = 0 then cover_c4 := true;
      if Bytes.exists (fun c -> Char.code c >= 0x80) tok then cover_c5 := true
    end
  done;
  (* fixed spot-checks: one per branch, mixed case (the prim is what makes them pass) *)
  List.iter
    (fun (tok, expect) ->
       let r = ref_ci_outcome (Bytes.of_string tok)
       and f = fast_ci_outcome (Bytes.of_string tok) in
       let e = Rkv.Rval.Int (Z.of_int expect) in
       if not (Rkv.Rval.equal r e && Rkv.Rval.equal f e) then begin
         incr ci_fails;
         Printf.printf "CI-DISPATCH SPOT FAIL (RSEED=%d) %S expected %d ref=%s fast=%s\n"
           seed tok expect (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
       end)
    [ ("NX", 1); ("nX", 1); ("Nx", 1); ("nx", 1);
      ("XX", 2); ("xX", 2); ("xx", 2);
      ("KEEPTTL", 0); ("KeepTtl", 0); ("", 0); ("n", 0); ("nxx", 0) ]

(* --- main ------------------------------------------------------------------ *)

let () =
  let n = 3000 in
  let fails = ref 0 in
  let successes = ref 0 in
  let errs = ref 0 in
  let ovfs = ref 0 in
  for _ = 1 to n do
    let input = gen_input () in
    let r = ref_outcome input in
    let f = fast_outcome input in
    note_input input r;
    (* record outcome class for logging *)
    (match r with
     | Rkv.Rval.Bytes ob ->
         if Bytes.equal ob err_bytes then incr errs
         else if Bytes.equal ob ovf_bytes then incr ovfs
         else incr successes
     | _ -> ());
    let eq = Rkv.Rval.equal r f in
    if not eq then begin
      incr fails;
      Printf.printf "MISMATCH (RSEED=%d) input=%s\n  ref=%s\n  fast=%s\n"
        seed (Rkv.Rval.to_string (Rkv.Rval.Bytes input))
        (Rkv.Rval.to_string r) (Rkv.Rval.to_string f)
    end
  done;

  (* Spot-check: G2 (int64_max) must produce OVF, not success *)
  let max_r = ref_outcome (Bytes.of_string "9223372036854775807") in
  (match max_r with
   | Rkv.Rval.Bytes b when Bytes.equal b ovf_bytes -> ()
   | v -> Printf.printf "SPOT-CHECK FAIL: int64_max+1 expected OVF, got %s\n" (Rkv.Rval.to_string v);
          incr fails);

  (* Spot-check: G1 ("0") must produce "1" *)
  let zero_r = ref_outcome (Bytes.of_string "0") in
  (match zero_r with
   | Rkv.Rval.Bytes b when Bytes.equal b (Bytes.of_string "1") -> ()
   | v -> Printf.printf "SPOT-CHECK FAIL: input \"0\" expected \"1\", got %s\n" (Rkv.Rval.to_string v);
          incr fails);

  (* Spot-check: G3 (int64_max+1) must produce ERR *)
  let over_r = ref_outcome (Bytes.of_string "9223372036854775808") in
  (match over_r with
   | Rkv.Rval.Bytes b when Bytes.equal b err_bytes -> ()
   | v -> Printf.printf "SPOT-CHECK FAIL: int64_max+1 string expected ERR, got %s\n" (Rkv.Rval.to_string v);
          incr fails);

  (* Spot-check: G6 ("0123") must produce ERR *)
  let lz_r = ref_outcome (Bytes.of_string "0123") in
  (match lz_r with
   | Rkv.Rval.Bytes b when Bytes.equal b err_bytes -> ()
   | v -> Printf.printf "SPOT-CHECK FAIL: \"0123\" expected ERR, got %s\n" (Rkv.Rval.to_string v);
          incr fails);

  direct_prim_pass ();
  ci_dispatch_pass ();

  let cov_ok =
    !cover_g1 && !cover_g2 && !cover_g3 && !cover_g4 && !cover_g5 &&
    !cover_g6 && !cover_g7 && !cover_g8 && !cover_g9 && !cover_g10 &&
    !cover_g11 && !cover_g12 && !cover_g13 && !cover_g14 && !cover_g15 &&
    !cover_g16
  in
  let ci_cov_ok = !cover_c1 && !cover_c2 && !cover_c3 && !cover_c4 && !cover_c5 in
  Printf.printf
    "states=%d fails=%d prim_fails=%d ci_fails=%d | outcomes: success=%d ERR=%d OVF=%d\n\
     coverage: G1(zero)=%b G2(max->OVF)=%b G3(parse-OOB-hi)=%b G4(min)=%b G5(parse-OOB-lo)=%b\n\
     G6(lead0)=%b G7(space)=%b G8(plus)=%b G9(empty)=%b G10(-0)=%b\n\
     G11(sci)=%b G12(20dig)=%b G13(junk)=%b G14(valid+)=%b G15(valid-)=%b G16(bare-)=%b\n\
     ci-dispatch: C1(nx-mixed)=%b C2(xx-mixed)=%b C3(default)=%b C4(empty)=%b C5(high)=%b\n"
    n !fails !prim_fails !ci_fails !successes !errs !ovfs
    !cover_g1 !cover_g2 !cover_g3 !cover_g4 !cover_g5
    !cover_g6 !cover_g7 !cover_g8 !cover_g9 !cover_g10
    !cover_g11 !cover_g12 !cover_g13 !cover_g14 !cover_g15 !cover_g16
    !cover_c1 !cover_c2 !cover_c3 !cover_c4 !cover_c5;
  if !fails = 0 && !prim_fails = 0 && !ci_fails = 0 && cov_ok && ci_cov_ok then
    print_endline "PRIMS DIFFERENTIAL OK: reference == fast (pipeline G1-G16 + all 17 realizers direct, case folds exhaustive over all 256 single bytes + ci-dispatch C1-C5 + list snoc order pinned); coverage asserted"
  else begin
    if not cov_ok then
      print_endline "PRIMS COVERAGE GAP: a required grammar class (G1-G16) was never exercised";
    if not ci_cov_ok then
      print_endline "PRIMS COVERAGE GAP: a required ci-dispatch class (C1-C5) was never exercised";
    exit 1
  end
