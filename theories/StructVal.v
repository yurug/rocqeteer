(** * StructVal — proofs and anti-vacuity for structured values (R7, adr-0010-structured-values).

    Every theorem below is fully proved by vm_compute (no unproved proof obligations, no
    axioms); Print Assumptions must read "Closed under the global context" for each.

    Contents:
    1. [sample_tag_build] reachable branches (success DTag/DPair/DList, overflow DTag) +
       an explicit-witness inhabitance lemma.
    2. [sample_tag_dispatch] reachable branches (PTag 0, PTag 1, default).
    3. Tag-collision observability: the same payload under tag 0 vs tag 1 gives different
       results, backed by a swapped-tags mutant that a correctness statement would reject.
    4. PTag-vs-mismatched-dval: Match falls to default on the right payload/wrong tag, and
       on a scrutinee that is not a DTag at all. *)

From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

(** Keep FMapAVL internals opaque so vm_compute only reduces the interpreter. *)
Opaque M.find M.add M.empty M.remove M.elements.

(* ===== §1  sample_tag_build reachable branches ============================ *)

(** Success path: context 5 -> PAddChecked 1 -> sum 6 -> tag 0, paired with the
    two-element mixed-shape list [42; tag_list_bytes]. *)
Theorem tag_build_success :
  let '(o, _) := run_top (DInt 5) sample_tag_build in
  o = ORet (DPair (DTag 0 (DInt 6)) (DList [DInt 42; DBytes tag_list_bytes])).
Proof. vm_compute. reflexivity. Qed.

(** Overflow path: context int64_max -> PAddChecked 1 overflows -> DNone -> tag 1
    with a DBytes payload. *)
Theorem tag_build_overflow :
  let '(o, _) := run_top (DInt int64_max) sample_tag_build in
  o = ORet (DTag 1 (DBytes tag_err_bytes)).
Proof. vm_compute. reflexivity. Qed.

(** Inhabitance of the success path, EXPLICIT witness (theories/Prims.v header note:
    [eexists. split; vm_compute] runs vm_compute on an open conjunct and degenerates —
    always give the witness up front). *)
Lemma tag_build_inhabited :
  exists w, run_top (DInt 5) sample_tag_build =
            (ORet (DPair (DTag 0 (DInt 6)) (DList [DInt 42; DBytes tag_list_bytes])), w).
Proof.
  exists (snd (run_top (DInt 5) sample_tag_build)).
  vm_compute. reflexivity.
Qed.

(* ===== §2  sample_tag_dispatch reachable branches ========================== *)

(** PTag 0 fires on a DTag 0 scrutinee (payload ignored by this program). *)
Theorem tag_dispatch_zero :
  let '(o, _) := run_top (DTag 0 (DInt 1)) sample_tag_dispatch in
  o = ORet (DBytes tag_dispatch_a_bytes).
Proof. vm_compute. reflexivity. Qed.

(** PTag 1 fires on a DTag 1 scrutinee. *)
Theorem tag_dispatch_one :
  let '(o, _) := run_top (DTag 1 (DBytes tag_list_bytes)) sample_tag_dispatch in
  o = ORet (DBytes tag_dispatch_b_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Default arm: a scrutinee that is not a DTag at all (a bare DInt) falls through. *)
Theorem tag_dispatch_default :
  let '(o, _) := run_top (DInt 42) sample_tag_dispatch in
  o = ORet (DBytes tag_dispatch_default_bytes).
Proof. vm_compute. reflexivity. Qed.

(* ===== §3  Tag-collision observability + swapped-tags mutant =============== *)

(** The SAME payload wrapped under tag 0 vs tag 1 gives DIFFERENT program results —
    the tag, not the payload, drives dispatch (adr-0010 §Consequences: tag discipline
    is genuinely observable, not accidental payload matching). *)
Theorem tag_collision_same_payload_diff_tag :
  (let '(o, _) := run_top (DTag 0 (DInt 1)) sample_tag_dispatch in o)
  <>
  (let '(o, _) := run_top (DTag 1 (DInt 1)) sample_tag_dispatch in o).
Proof. vm_compute. intro H. discriminate H. Qed.

(** Mutant: swap the two PTag branch BODIES (patterns/tags unchanged) — same style as
    Dispatch.v's swapped-branches mutant and Prims.v's lenient-parse mutant. *)
Definition sample_tag_dispatch_swapped : tm :=
  Bind (Perform OAsk [])
       (Match (VVar 0)
          [(PTag 0, Ret (VBytes tag_dispatch_b_bytes));
           (PTag 1, Ret (VBytes tag_dispatch_a_bytes))]
          (Ret (VBytes tag_dispatch_default_bytes))).

(** The mutant sends tag 0 to "TG1" (the body that belongs to tag 1 in the real program). *)
Theorem tag_dispatch_swapped_on_tag0 :
  let '(o, _) := run_top (DTag 0 (DInt 1)) sample_tag_dispatch_swapped in
  o = ORet (DBytes tag_dispatch_b_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Therefore the mutant is OBSERVABLY DIFFERENT from the correct program on tag 0 —
    a correctness statement for [sample_tag_dispatch] genuinely rejects this mutant. *)
Theorem tag_dispatch_swapped_differs_from_correct :
  (let '(o, _) := run_top (DTag 0 (DInt 1)) sample_tag_dispatch in o)
  <>
  (let '(o, _) := run_top (DTag 0 (DInt 1)) sample_tag_dispatch_swapped in o).
Proof. vm_compute. intro H. discriminate H. Qed.

(* ===== §4  PTag vs. a mismatched dval ======================================= *)

(** Right "kind" of payload (DInt 1, same shape as the tag-0/tag-1 branches accept),
    but the WRONG tag (7) — Match falls through to the default arm. *)
Theorem tag_dispatch_wrong_tag_falls_default :
  let '(o, _) := run_top (DTag 7 (DInt 1)) sample_tag_dispatch in
  o = ORet (DBytes tag_dispatch_default_bytes).
Proof. vm_compute. reflexivity. Qed.

(** A scrutinee that is NOT a DTag at all (DUnit here, distinct from the DInt case
    already covered by [tag_dispatch_default]) also falls to the default arm. *)
Theorem tag_dispatch_notag_falls_default :
  let '(o, _) := run_top DUnit sample_tag_dispatch in
  o = ORet (DBytes tag_dispatch_default_bytes).
Proof. vm_compute. reflexivity. Qed.

(** Print Assumptions footprint — each must say "Closed under the global context". *)
Print Assumptions tag_build_success.
Print Assumptions tag_build_overflow.
Print Assumptions tag_build_inhabited.
Print Assumptions tag_dispatch_zero.
Print Assumptions tag_dispatch_one.
Print Assumptions tag_dispatch_default.
Print Assumptions tag_collision_same_payload_diff_tag.
Print Assumptions tag_dispatch_swapped_on_tag0.
Print Assumptions tag_dispatch_swapped_differs_from_correct.
Print Assumptions tag_dispatch_wrong_tag_falls_default.
Print Assumptions tag_dispatch_notag_falls_default.
