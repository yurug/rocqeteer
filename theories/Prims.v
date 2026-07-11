(** * Prims — proofs and anti-vacuity for the v1 primitive set (adr-0009-vprim-registry).

    All theorems are Print-Assumptions-closed ("Closed under the global context");
    no admitted proofs, no axioms.

    Contents:
    1. [parse_print_roundtrip_*]: parse (print z) = DSome (DInt z) for concrete in-range values.
    2. Strict-grammar rejection lemmas (one per violation class), proved by vm_compute.
    3. Overflow rejection (PAddChecked at boundary).
    4. [sample_parse] program proofs (success, ERR, OVF branches; inhabitance; mutant rejection). *)

From Stdlib Require Import ZArith List Ascii String Bool.
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

(** The round-trip law is verified at all critical boundary values below (zero, ±1, and
    the exact int64 boundaries) using vm_compute. These instances cover the full
    domain boundary of in_range and collectively serve as the anti-vacuity corpus.
    A general parametric proof requires a stdlib lemma connecting NilEmpty.string_of_uint
    with apply_parse_int64 — deferred to a future formal development task. *)

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
  let '(o, _) := run_top (DBytes (list_ascii_of_string "42")) sample_parse in
  o = ORet (DBytes (list_ascii_of_string "43")).
Proof. vm_compute. reflexivity. Qed.

(** Error path: input "0123" (leading zero) → parse DNone → ERR branch. *)
Theorem sample_parse_reject_leading_zero :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Error path: empty input → parse DNone → ERR branch. *)
Theorem sample_parse_reject_empty :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "")) sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Error path: "+5" → DNone → ERR branch. *)
Theorem sample_parse_reject_plus :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "+5")) sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Error path: " 5" → DNone → ERR branch. *)
Theorem sample_parse_reject_space :
  let '(o, _) := run_top (DBytes (list_ascii_of_string " 5")) sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Error path: "-0" → DNone → ERR branch. *)
Theorem sample_parse_reject_minus_zero :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "-0")) sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Overflow path: int64_max → parse succeeds → add 1 → PAddChecked DNone → OVF branch. *)
Theorem sample_parse_overflow :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "9223372036854775807")) sample_parse in
  o = ORet (DBytes ovf_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Inhabitance of the success path: there exists a world where "42" gives "43". *)
Lemma sample_parse_inhabited :
  exists w, run_top (DBytes (list_ascii_of_string "42")) sample_parse =
            (ORet (DBytes (list_ascii_of_string "43")), w).
Proof.
  exists (snd (run_top (DBytes (list_ascii_of_string "42")) sample_parse)).
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
  let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) sample_parse_lenient in
  o = ORet (DBytes (list_ascii_of_string "OK")).
Proof. vm_compute. reflexivity. Qed.

(** The strict parser REJECTS "0123" (returns err_bytes). *)
Theorem strict_rejects_leading_zero :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) sample_parse in
  o = ORet (DBytes err_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Therefore the two programs differ on "0123" — the mutant is observably different: *)
Theorem mutant_differs_from_strict :
  (let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) sample_parse_lenient in o)
  <>
  (let '(o, _) := run_top (DBytes (list_ascii_of_string "0123")) sample_parse in o).
Proof. vm_compute. intro H. discriminate H. Qed.

(** Print Assumptions footprint — each must say "Closed under the global context". *)
Print Assumptions parse_print_zero.
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
