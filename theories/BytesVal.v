(** * BytesVal — anti-vacuity proof for sample_bytes (invariant 4).

    We prove by vm_compute that [sample_bytes] starting from an empty store:
      (1) returns [DBytes bytes_payload] — the value stored is recovered verbatim;
      (2) leaves the store with the binding key "5" -> (DBytes bytes_payload, None).

    A proof-mutation check proves the wrong program [sample_bytes_wrong] is rejected:
    a program that stores a DIFFERENT byte string cannot satisfy the spec, so the
    correctness statement genuinely constrains [sample_bytes].

    R4 (adr-0011): keys are byte strings; [run_top] takes the run's instant [now].

    [Print Assumptions bytes_correct] is expected to be "Closed under the global context". *)

From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Correctness: sample_bytes from empty returns the stored value.

    From the empty world, [sample_bytes] does:
      Put "5" (DBytes payload)  ->  Get "5"  ->  Match/PSome binds payload  ->  Ret (VVar 0)
    The outcome is [ORet (DBytes bytes_payload)] and the store has key "5" (no deadline —
    OPut clears/never sets one). *)
Theorem bytes_correct :
  let '(outcome, w) := run_top DUnit 0 sample_bytes in
  outcome = ORet (DBytes bytes_payload) /\
  M.find (string_of_list_ascii key5) (kv w) = Some (DBytes bytes_payload, None).
Proof. vm_compute. repeat split. Qed.

(** ** Inhabitance: the precondition (empty initial state) is trivially satisfied,
    so [bytes_correct] is not vacuously true. Explicit witness (theories/Prims.v header). *)
Lemma bytes_correct_inhabited : exists w,
  run_top DUnit 0 sample_bytes = (ORet (DBytes bytes_payload), w).
Proof.
  exists (snd (run_top DUnit 0 sample_bytes)).
  vm_compute. reflexivity.
Qed.

(** ** Proof-mutation check: a program that stores DIFFERENT bytes (empty list) is
    rejected: the spec says the result is [DBytes bytes_payload] (length 6), the mutant
    returns [DBytes []]. *)
Definition sample_bytes_wrong : tm :=
  Bind (Perform OPut [VBytes key5; VBytes []])
       (Bind (Perform OGet [VBytes key5])
             (Match (VVar 0)
                [(PNone, Ret VNone);
                 (PSome, Ret (VVar 0))]
                (Ret VNone))).

(** The wrong program returns [DBytes []] (empty), not [DBytes bytes_payload]. *)
Lemma bytes_wrong_outcome :
  let '(outcome, _) := run_top DUnit 0 sample_bytes_wrong in
  outcome = ORet (DBytes []).
Proof. vm_compute. reflexivity. Qed.

(** The mutant output differs from the correct output:
    [DBytes []] ≠ [DBytes bytes_payload] — the payload is non-empty. *)
Lemma bytes_wrong_differs : ORet (DBytes []) <> ORet (DBytes bytes_payload).
Proof. unfold bytes_payload. discriminate. Qed.

(** Proof-mutation gate: [sample_bytes_wrong] (which stores [DBytes []]) cannot satisfy
    the correctness statement for [sample_bytes] (which requires [DBytes bytes_payload]). *)
Theorem bytes_wrong_rejected :
  ~ (let '(outcome, _) := run_top DUnit 0 sample_bytes_wrong in
     outcome = ORet (DBytes bytes_payload)).
Proof. vm_compute. intro H. discriminate H. Qed.

(** Surface the assumption footprint — must say "Closed under the global context". *)
Print Assumptions bytes_correct.
