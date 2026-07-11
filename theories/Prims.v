(** * Prims — proofs and anti-vacuity for the v1 primitive set (adr-0009-vprim-registry).

    All theorems are Print-Assumptions-closed ("Closed under the global context");
    no admitted proofs, no axioms.

    Contents:
    1. [parse_print_*]: parse (print z) = DSome (DInt z) — concrete boundary instances,
       then the general [parse_print_roundtrip] for ALL in-range z (§1b).
    2. Strict-grammar rejection lemmas (one per violation class), proved by vm_compute.
    3. Overflow rejection (PAddChecked at boundary).
    4. [sample_parse] program proofs (success, ERR, OVF branches; inhabitance; mutant rejection). *)

From Stdlib Require Import ZArith List Ascii String Bool Lia.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

(** Keep FMapAVL internals opaque so vm_compute only reduces the interpreter. *)
Opaque M.find M.add M.empty M.remove M.elements.

(* ===== §1  Parse / Print round-trip ====================================== *)

(** [parse_print_roundtrip]: for any in-range z,
    [apply_prim PPrintInt [DInt z]] = [DSome (DBytes bs)] for some bs,
    and [apply_prim PParseInt64 [DBytes bs]] = [DSome (DInt z)].

    We prove this for the critical concrete values using vm_compute.

    NB: witnesses are EXPLICIT, not [eexists] — [split; vm_compute] would run vm_compute
    on the parse conjunct while the witness evar is still uninstantiated, and vm_compute
    on an open term degenerates (observed: multi-GB blowup, OOM-killed builds). *)

Theorem parse_print_zero :
  exists bs,
    apply_prim PPrintInt [DInt 0] = DSome (DBytes bs) /\
    apply_prim PParseInt64 [DBytes bs] = DSome (DInt 0).
Proof. exists (list_ascii_of_string "0"). split; vm_compute; reflexivity. Qed.

Theorem parse_print_one :
  exists bs,
    apply_prim PPrintInt [DInt 1] = DSome (DBytes bs) /\
    apply_prim PParseInt64 [DBytes bs] = DSome (DInt 1).
Proof. exists (list_ascii_of_string "1"). split; vm_compute; reflexivity. Qed.

Theorem parse_print_neg_one :
  exists bs,
    apply_prim PPrintInt [DInt (-1)] = DSome (DBytes bs) /\
    apply_prim PParseInt64 [DBytes bs] = DSome (DInt (-1)).
Proof. exists (list_ascii_of_string "-1"). split; vm_compute; reflexivity. Qed.

Theorem parse_print_max :
  exists bs,
    apply_prim PPrintInt [DInt int64_max] = DSome (DBytes bs) /\
    apply_prim PParseInt64 [DBytes bs] = DSome (DInt int64_max).
Proof.
  exists (list_ascii_of_string "9223372036854775807").
  split; vm_compute; reflexivity.
Qed.

Theorem parse_print_min :
  exists bs,
    apply_prim PPrintInt [DInt int64_min] = DSome (DBytes bs) /\
    apply_prim PParseInt64 [DBytes bs] = DSome (DInt int64_min).
Proof.
  exists (list_ascii_of_string "-9223372036854775808").
  split; vm_compute; reflexivity.
Qed.

(** The round-trip law is verified above at the critical boundary values (zero, ±1, and
    the exact int64 boundaries) using vm_compute. These instances cover the full
    domain boundary of in_range and collectively serve as the anti-vacuity corpus.
    The GENERAL theorem [parse_print_roundtrip] below proves the law for EVERY in-range z,
    via the printing spec [print_digits_fuel_spec] (no stdlib DecimalString needed). *)

(* ===== §1b  General parse/print round-trip ================================ *)

(** [ascii_eqb] is sound (bit-by-bit Bool.eqb comparison) and reflexive. *)
Lemma ascii_eqb_eq : forall a b : ascii, ascii_eqb a b = true -> a = b.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7] H.
  cbn in H.
  repeat match goal with
         | H : andb _ _ = true |- _ => apply andb_prop in H; destruct H
         end.
  repeat match goal with
         | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
         end.
  subst; reflexivity.
Qed.

Lemma ascii_eqb_refl : forall a : ascii, ascii_eqb a a = true.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7]; cbn.
  now rewrite !Bool.eqb_reflx.
Qed.

(** A digit character is not '-' (ASCII 45 < 48). *)
Lemma digit_not_minus : forall c,
  is_digit c = true -> ascii_eqb c (ascii_of_N 45) = false.
Proof.
  intros c H.
  destruct (ascii_eqb c (ascii_of_N 45)) eqn:E; [|reflexivity].
  apply ascii_eqb_eq in E. subst c. vm_compute in H. discriminate H.
Qed.

(** A character strictly above '0' (48) is not '0'. *)
Lemma above_48_not_zero : forall c,
  (48 < N_of_ascii c)%N -> ascii_eqb c (ascii_of_N 48) = false.
Proof.
  intros c H.
  destruct (ascii_eqb c (ascii_of_N 48)) eqn:E; [|reflexivity].
  apply ascii_eqb_eq in E. subst c. vm_compute in H. discriminate H.
Qed.

(** Characters built as [48 + d] with d < 10 are digits, with the expected value
    (the ascii/N embedding is faithful below 256). *)
Lemma N_of_ascii_digit : forall d : N, (d < 10)%N ->
  N_of_ascii (ascii_of_N (48 + d)) = (48 + d)%N.
Proof. intros d Hd. apply N_ascii_embedding. lia. Qed.

Lemma is_digit_48_plus : forall d : N, (d < 10)%N ->
  is_digit (ascii_of_N (48 + d)) = true.
Proof.
  intros d Hd. unfold is_digit. rewrite N_of_ascii_digit by exact Hd.
  apply andb_true_intro. split; apply N.leb_le; lia.
Qed.

Lemma digit_val_48_plus : forall d : N, (d < 10)%N ->
  digit_val (ascii_of_N (48 + d)) = Z.of_N d.
Proof.
  intros d Hd. unfold digit_val. rewrite N_of_ascii_digit by exact Hd. lia.
Qed.

(** [parse_digits] distributes over append (the accumulator threads through). *)
Lemma parse_digits_app : forall ds1 ds2 acc,
  parse_digits (ds1 ++ ds2) acc = parse_digits ds2 (parse_digits ds1 acc).
Proof.
  induction ds1 as [|c ds1 IH]; intros ds2 acc; cbn; [reflexivity | apply IH].
Qed.

(** Core printing spec: with enough fuel ([n < 10^fuel]), [print_digits_fuel] on a
    positive [n] emits a nonempty MSB-first digit string prepended to [acc], whose
    leading digit is nonzero, and which [parse_digits] maps back to [n]. *)
Lemma print_digits_fuel_spec : forall fuel (n : N) (acc : list ascii),
  (n < 10 ^ N.of_nat fuel)%N ->
  (0 < n)%N ->
  exists ds,
    print_digits_fuel fuel n acc = ds ++ acc /\
    forallb is_digit ds = true /\
    (exists d0 ds', ds = d0 :: ds' /\ (48 < N_of_ascii d0)%N) /\
    parse_digits ds 0 = Z.of_N n.
Proof.
  induction fuel as [|f' IH]; intros n acc Hlt Hpos.
  - (* fuel = 0: n < 10^0 = 1 contradicts 0 < n *)
    cbn in Hlt. lia.
  - assert (Hdm := N.div_mod' n 10).
    assert (Hm10 : (n mod 10 < 10)%N) by (apply N.mod_upper_bound; discriminate).
    destruct (n / 10)%N as [|q] eqn:Hq.
    + (* n < 10: single (hence leading, hence nonzero) digit *)
      assert (Hstep : print_digits_fuel (S f') n acc = ascii_of_N (48 + n mod 10) :: acc).
      { cbn [print_digits_fuel]. rewrite Hq. reflexivity. }
      exists [ascii_of_N (48 + n mod 10)].
      rewrite Hstep.
      split; [reflexivity|].
      split.
      { cbn [forallb]. now rewrite is_digit_48_plus by exact Hm10. }
      split.
      { exists (ascii_of_N (48 + n mod 10)), [].
        split; [reflexivity|].
        rewrite N_of_ascii_digit by exact Hm10. lia. }
      cbn [parse_digits].
      rewrite digit_val_48_plus by exact Hm10. lia.
    + (* n = 10*q + r with q > 0: recurse on q, append the digit of r *)
      assert (Hstep : print_digits_fuel (S f') n acc
                      = print_digits_fuel f' (N.pos q) (ascii_of_N (48 + n mod 10) :: acc)).
      { cbn [print_digits_fuel]. rewrite Hq. reflexivity. }
      assert (Hq' : (N.pos q < 10 ^ N.of_nat f')%N).
      { rewrite <- Hq. apply N.Div0.div_lt_upper_bound.
        replace (N.of_nat (S f')) with (N.succ (N.of_nat f')) in Hlt by lia.
        rewrite N.pow_succ_r' in Hlt. exact Hlt. }
      destruct (IH (N.pos q) (ascii_of_N (48 + n mod 10) :: acc) Hq' ltac:(lia))
        as (ds & Hprint & Hall & (d0 & ds' & Hcons & Hd0) & Hparse).
      exists (ds ++ [ascii_of_N (48 + n mod 10)]).
      split.
      { rewrite Hstep, Hprint, <- app_assoc. reflexivity. }
      split.
      { rewrite forallb_app, Hall. cbn [forallb].
        now rewrite is_digit_48_plus by exact Hm10. }
      split.
      { exists d0, (ds' ++ [ascii_of_N (48 + n mod 10)]).
        subst ds. split; [reflexivity | exact Hd0]. }
      rewrite parse_digits_app. cbn [parse_digits].
      rewrite Hparse, digit_val_48_plus by exact Hm10.
      lia.
Qed.

(** Walking [apply_parse_int64] on an unsigned digit string: nonzero leading digit,
    all-digit body, in-range value → DSome. The [cbv beta iota zeta] steps reduce
    exactly the exposed match/let redexes (no delta), keeping rewrites syntactic. *)
Lemma apply_parse_int64_digits : forall d0 ds z,
  is_digit d0 = true ->
  (48 < N_of_ascii d0)%N ->
  forallb is_digit ds = true ->
  parse_digits (d0 :: ds) 0 = z ->
  in_range z = true ->
  apply_parse_int64 (d0 :: ds) = DSome (DInt z).
Proof.
  intros d0 ds z Hdig Hd0 Hall Hval Hrange.
  unfold apply_parse_int64. cbv beta iota zeta.
  rewrite (digit_not_minus d0 Hdig). cbv beta iota zeta.
  rewrite Hdig. cbv beta iota zeta delta [negb].
  rewrite (above_48_not_zero d0 Hd0). cbv beta iota zeta.
  rewrite Hall. cbv beta iota zeta.
  rewrite Hval, Hrange. reflexivity.
Qed.

(** Same walk for a '-'-prefixed digit string (DP2 strips the sign, DP7 negates). *)
Lemma apply_parse_int64_neg_digits : forall d0 ds z,
  is_digit d0 = true ->
  (48 < N_of_ascii d0)%N ->
  forallb is_digit ds = true ->
  parse_digits (d0 :: ds) 0 = z ->
  in_range (- z) = true ->
  apply_parse_int64 (ascii_of_N 45 :: d0 :: ds) = DSome (DInt (- z)).
Proof.
  intros d0 ds z Hdig Hd0 Hall Hval Hrange.
  unfold apply_parse_int64. cbv beta iota zeta.
  rewrite (ascii_eqb_refl (ascii_of_N 45)). cbv beta iota zeta.
  rewrite Hdig. cbv beta iota zeta delta [negb].
  rewrite (above_48_not_zero d0 Hd0). cbv beta iota zeta.
  rewrite Hall. cbv beta iota zeta.
  rewrite Hval, Hrange. reflexivity.
Qed.

(** [apply_print_int] unfolded on the two nonzero shapes. *)
Lemma apply_print_int_pos : forall p : positive,
  in_range (Z.pos p) = true ->
  apply_print_int (Z.pos p) = DSome (DBytes (print_digits_fuel 20 (N.pos p) [])).
Proof. intros p Hr. unfold apply_print_int. rewrite Hr. reflexivity. Qed.

Lemma apply_print_int_neg : forall p : positive,
  in_range (Z.neg p) = true ->
  apply_print_int (Z.neg p)
  = DSome (DBytes (ascii_of_N 45 :: print_digits_fuel 20 (N.pos p) [])).
Proof. intros p Hr. unfold apply_print_int. rewrite Hr. reflexivity. Qed.

(** Fuel 20 suffices: any in-range magnitude is at most 2^63 = 9223372036854775808,
    and 2^63 < 10^20. *)
Lemma int64_mag_lt_pow10_20 : forall m : N,
  (m <= 9223372036854775808)%N -> (m < 10 ^ N.of_nat 20)%N.
Proof.
  intros m Hm. eapply N.le_lt_trans; [exact Hm | vm_compute; reflexivity].
Qed.

(** THE GENERAL ROUND-TRIP THEOREM: for every in-range z, printing succeeds and
    parsing the printed bytes recovers exactly z. Subsumes the concrete instances
    above (which remain as the vm_compute anti-vacuity corpus). *)
Theorem parse_print_roundtrip :
  forall z : Z, in_range z = true ->
    exists bs, apply_prim PPrintInt [DInt z] = DSome (DBytes bs) /\
               apply_prim PParseInt64 [DBytes bs] = DSome (DInt z).
Proof.
  intros z Hr.
  destruct z as [|p|p].
  - (* z = 0 : concrete *)
    exists [ascii_of_N 48]. split; vm_compute; reflexivity.
  - (* z = Z.pos p *)
    assert (Hhi : Z.pos p <= int64_max).
    { generalize Hr; unfold in_range; intros HH.
      apply andb_prop in HH as [_ HH]. now apply Z.leb_le. }
    assert (Hb : (N.pos p < 10 ^ N.of_nat 20)%N).
    { apply int64_mag_lt_pow10_20. unfold int64_max in Hhi. lia. }
    destruct (print_digits_fuel_spec 20 (N.pos p) [] Hb ltac:(lia))
      as (ds & Hprint & Hall & (d0 & ds' & Hcons & Hd0) & Hparse).
    subst ds. rewrite app_nil_r in Hprint.
    exists (d0 :: ds').
    split.
    + change (apply_prim PPrintInt [DInt (Z.pos p)]) with (apply_print_int (Z.pos p)).
      rewrite (apply_print_int_pos p Hr), Hprint. reflexivity.
    + change (apply_prim PParseInt64 [DBytes (d0 :: ds')])
        with (apply_parse_int64 (d0 :: ds')).
      cbn [forallb] in Hall. apply andb_prop in Hall as [Hd0dig Hall].
      apply apply_parse_int64_digits.
      * exact Hd0dig.
      * exact Hd0.
      * exact Hall.
      * exact Hparse.  (* Z.of_N (N.pos p) is convertible to Z.pos p *)
      * exact Hr.
  - (* z = Z.neg p *)
    assert (Hlo : int64_min <= Z.neg p).
    { generalize Hr; unfold in_range; intros HH.
      apply andb_prop in HH as [HH _]. now apply Z.leb_le. }
    assert (Hb : (N.pos p < 10 ^ N.of_nat 20)%N).
    { apply int64_mag_lt_pow10_20. unfold int64_min in Hlo. lia. }
    destruct (print_digits_fuel_spec 20 (N.pos p) [] Hb ltac:(lia))
      as (ds & Hprint & Hall & (d0 & ds' & Hcons & Hd0) & Hparse).
    subst ds. rewrite app_nil_r in Hprint.
    exists (ascii_of_N 45 :: d0 :: ds').
    split.
    + change (apply_prim PPrintInt [DInt (Z.neg p)]) with (apply_print_int (Z.neg p)).
      rewrite (apply_print_int_neg p Hr), Hprint. reflexivity.
    + change (apply_prim PParseInt64 [DBytes (ascii_of_N 45 :: d0 :: ds')])
        with (apply_parse_int64 (ascii_of_N 45 :: d0 :: ds')).
      cbn [forallb] in Hall. apply andb_prop in Hall as [Hd0dig Hall].
      change (Z.neg p) with (- Z.pos p).
      apply apply_parse_int64_neg_digits.
      * exact Hd0dig.
      * exact Hd0.
      * exact Hall.
      * exact Hparse.  (* Z.of_N (N.pos p) is convertible to Z.pos p *)
      * exact Hr.      (* in_range (- Z.pos p) is convertible to in_range (Z.neg p) *)
Qed.

(* ===== §2  Strict-grammar rejection lemmas ================================ *)
(** Each lemma is proved by vm_compute on a concrete violating input. *)

(** Helper: decode a string as a DBytes for passing to PParseInt64. *)
Definition parse_str (s : string) : dval :=
  apply_prim PParseInt64 [DBytes (list_ascii_of_string s)].

(** DP1: empty input → DNone. *)
Theorem parse_reject_empty :
  parse_str "" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP4: leading zero with more digits → DNone ("0123"). *)
Theorem parse_reject_leading_zero :
  parse_str "0123" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP5: leading '+' → DNone. *)
Theorem parse_reject_leading_plus :
  parse_str "+5" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP5: leading space → DNone. *)
Theorem parse_reject_leading_space :
  parse_str " 5" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP3: bare '-' → DNone. *)
Theorem parse_reject_minus_only :
  parse_str "-" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP4 + sign: "-0" → DNone (not canonical). *)
Theorem parse_reject_minus_zero :
  parse_str "-0" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP5: non-digit in body → DNone ("1e3"). *)
Theorem parse_reject_sci_notation :
  parse_str "1e3" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP5: trailing junk → DNone ("123abc"). *)
Theorem parse_reject_trailing_junk :
  parse_str "123abc" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP8: out of range above int64_max → DNone ("9223372036854775808"). *)
Theorem parse_reject_overflow_max :
  parse_str "9223372036854775808" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP8: out of range below int64_min → DNone ("-9223372036854775809"). *)
Theorem parse_reject_overflow_min :
  parse_str "-9223372036854775809" = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP1: non-digit bytes (binary junk, NUL byte) → DNone. *)
Theorem parse_reject_binary_junk :
  apply_prim PParseInt64 [DBytes [Ascii false false false false false false false false]] = DNone.
Proof. vm_compute. reflexivity. Qed.

(** DP5: 20+ digit number exceeding int64 → DNone. *)
Theorem parse_reject_twenty_digits :
  parse_str "99999999999999999999" = DNone.
Proof. vm_compute. reflexivity. Qed.

(* ===== §3  Successful parse cases ========================================= *)

Theorem parse_accept_zero :
  parse_str "0" = DSome (DInt 0).
Proof. vm_compute. reflexivity. Qed.

Theorem parse_accept_max :
  parse_str "9223372036854775807" = DSome (DInt 9223372036854775807).
Proof. vm_compute. reflexivity. Qed.

Theorem parse_accept_min :
  parse_str "-9223372036854775808" = DSome (DInt (-9223372036854775808)).
Proof. vm_compute. reflexivity. Qed.

(* ===== §4  Overflow path of PAddChecked =================================== *)

(** Adding 1 to int64_max overflows → DNone. *)
Theorem add_checked_overflow :
  apply_prim PAddChecked [DInt int64_max; DInt 1] = DNone.
Proof. vm_compute. reflexivity. Qed.

(** Adding within range succeeds. *)
Theorem add_checked_ok :
  apply_prim PAddChecked [DInt 10; DInt 20] = DSome (DInt 30).
Proof. vm_compute. reflexivity. Qed.

(** Subtracting beyond int64_min overflows → DNone. *)
Theorem sub_checked_overflow :
  apply_prim PSubChecked [DInt int64_min; DInt 1] = DNone.
Proof. vm_compute. reflexivity. Qed.

(* ===== §5  sample_parse program correctness ================================ *)
(** [sample_parse] is defined in Samples.v. It takes a DBytes context (OAsk), parses it,
    on DSome → PAddChecked 1 → PPrintInt; on DNone / AddChecked failure → Ret (VBytes err/ovf). *)

(** Success path: input "42" → parse succeeds (z=42) → add 1 → z=43 → print → "43". *)
Theorem sample_parse_success :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "42")) 0 sample_parse in
  o = ORet (DBytes (list_ascii_of_string "43")).
Proof. vm_compute. reflexivity. Qed.

(** Error path: input "0123" (leading zero) → parse DNone → ERR branch. *)
Theorem sample_parse_reject_leading_zero :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) 0 sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Error path: empty input → parse DNone → ERR branch. *)
Theorem sample_parse_reject_empty :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "")) 0 sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Error path: "+5" → DNone → ERR branch. *)
Theorem sample_parse_reject_plus :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "+5")) 0 sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Error path: " 5" → DNone → ERR branch. *)
Theorem sample_parse_reject_space :
  let '(o, _) := run_top (DBytes (list_ascii_of_string " 5")) 0 sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Error path: "-0" → DNone → ERR branch. *)
Theorem sample_parse_reject_minus_zero :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "-0")) 0 sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Overflow path: int64_max → parse succeeds → add 1 → PAddChecked DNone → OVF branch. *)
Theorem sample_parse_overflow :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "9223372036854775807")) 0 sample_parse in
  o = ORet (DBytes ovf_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Inhabitance of the success path: there exists a world where "42" gives "43". *)
Lemma sample_parse_inhabited :
  exists w, run_top (DBytes (list_ascii_of_string "42")) 0 sample_parse =
            (ORet (DBytes (list_ascii_of_string "43")), w).
Proof.
  exists (snd (run_top (DBytes (list_ascii_of_string "42")) 0 sample_parse)).
  vm_compute. reflexivity.
Qed.

(** Mutant rejection: a LENIENT parse program that accepts "0123" (returns "OK" for any
    non-empty input) would NOT satisfy the rejection spec — proving the strict grammar is
    genuinely enforced by our definition, not vacuously. *)
Definition sample_parse_lenient : tm :=
  Bind (Perform OAsk [])
       (Match (VVar 0)
          [(PBytes [], Ret (VBytes err_bytes))]
          (Ret (VBytes (list_ascii_of_string "OK")))).

(** The lenient mutant ACCEPTS "0123" (returns "OK"). *)
Theorem mutant_lenient_accepts_leading_zero :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) 0 sample_parse_lenient in
  o = ORet (DBytes (list_ascii_of_string "OK")).
Proof. vm_compute. reflexivity. Qed.

(** The strict parser REJECTS "0123" (returns err_bytes). *)
Theorem strict_rejects_leading_zero :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) 0 sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Therefore the two programs differ on "0123" — the mutant is observably different: *)
Theorem mutant_differs_from_strict :
  (let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) 0 sample_parse_lenient in o)
  <>
  (let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) 0 sample_parse in o).
Proof. vm_compute. intro H. discriminate H. Qed.

(** Print Assumptions footprint — each must say "Closed under the global context". *)
Print Assumptions parse_print_zero.
Print Assumptions parse_print_roundtrip.
Print Assumptions parse_print_one.
Print Assumptions parse_print_neg_one.
Print Assumptions parse_print_max.
Print Assumptions parse_print_min.
Print Assumptions parse_reject_empty.
Print Assumptions parse_reject_leading_zero.
Print Assumptions parse_reject_leading_plus.
Print Assumptions parse_reject_leading_space.
Print Assumptions parse_reject_minus_only.
Print Assumptions parse_reject_minus_zero.
Print Assumptions parse_reject_sci_notation.
Print Assumptions parse_reject_overflow_max.
Print Assumptions parse_reject_overflow_min.
Print Assumptions add_checked_overflow.
Print Assumptions sub_checked_overflow.
Print Assumptions sample_parse_success.
Print Assumptions sample_parse_overflow.
Print Assumptions sample_parse_inhabited.
Print Assumptions mutant_differs_from_strict.
