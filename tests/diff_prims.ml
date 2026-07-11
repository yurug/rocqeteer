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
    Reference == fast byte-identical is asserted for every tested input. *)

module E   = Ref_extracted.EffIR
module D   = Ref_extracted.Datatypes
module S   = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

(* --- reference side -------------------------------------------------------- *)

(** Run [sample_parse] with a Bytes context; extract the outcome. *)
let ref_outcome (ctx_bytes : bytes) : Rkv.Rval.t =
  let coq_ctx = E.DBytes (Coqconv.bytes_to_ascii_list ctx_bytes) in
  match E.run_top coq_ctx S.sample_parse with
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
     | _ -> ())
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
  (* shape mismatches: both sides must agree on DNone *)
  check_prim "add_checked" E.PAddChecked (app2 Rkv.Prims.prim_add_checked)
    [Rkv.Rval.Bytes (Bytes.of_string "1"); Rkv.Rval.Int Z.one];
  check_prim "bytes_len" E.PBytesLen (app1 Rkv.Prims.prim_bytes_len) [Rkv.Rval.Int Z.zero];
  check_prim "eq_bytes" E.PEqBytes (app2 Rkv.Prims.prim_eq_bytes)
    [Rkv.Rval.Unit; Rkv.Rval.Bytes Bytes.empty]

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

  let cov_ok =
    !cover_g1 && !cover_g2 && !cover_g3 && !cover_g4 && !cover_g5 &&
    !cover_g6 && !cover_g7 && !cover_g8 && !cover_g9 && !cover_g10 &&
    !cover_g11 && !cover_g12 && !cover_g13 && !cover_g14 && !cover_g15 &&
    !cover_g16
  in
  Printf.printf
    "states=%d fails=%d prim_fails=%d | outcomes: success=%d ERR=%d OVF=%d\n\
     coverage: G1(zero)=%b G2(max->OVF)=%b G3(parse-OOB-hi)=%b G4(min)=%b G5(parse-OOB-lo)=%b\n\
     G6(lead0)=%b G7(space)=%b G8(plus)=%b G9(empty)=%b G10(-0)=%b\n\
     G11(sci)=%b G12(20dig)=%b G13(junk)=%b G14(valid+)=%b G15(valid-)=%b G16(bare-)=%b\n"
    n !fails !prim_fails !successes !errs !ovfs
    !cover_g1 !cover_g2 !cover_g3 !cover_g4 !cover_g5
    !cover_g6 !cover_g7 !cover_g8 !cover_g9 !cover_g10
    !cover_g11 !cover_g12 !cover_g13 !cover_g14 !cover_g15 !cover_g16;
  if !fails = 0 && !prim_fails = 0 && cov_ok then
    print_endline "PRIMS DIFFERENTIAL OK: reference == fast (pipeline G1-G16 + all 9 realizers direct); coverage asserted"
  else begin
    if not cov_ok then
      print_endline "PRIMS COVERAGE GAP: a required grammar class (G1-G16) was never exercised";
    exit 1
  end
