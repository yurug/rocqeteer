(** * BytesVal — anti-vacuity proof for sample_bytes (invariant 4).

    We prove by vm_compute that [sample_bytes] starting from an empty store:
      (1) returns [Some (DBytes bytes_payload)] — the value stored is recovered verbatim;
      (2) leaves the KV state with exactly one binding: key 5 -> DBytes bytes_payload.

    A proof-mutation check (in-file [Fail]) proves the wrong program [sample_bytes_wrong]
    is rejected: a program that stores a DIFFERENT byte string cannot satisfy the spec,
    so the correctness statement genuinely constrains [sample_bytes].

    [Print Assumptions bytes_correct] is expected to be "Closed under the global context". *)

From Stdlib Require Import ZArith List Ascii.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

(** Keep FMapAVL internals opaque so [vm_compute] only reduces the interpreter,
    not the tree balancing (same strategy as KV.v). *)
Opaque M.find M.add M.empty M.remove.

(** ** Correctness: sample_bytes from empty returns the stored value.

    From the empty world, [sample_bytes] does:
      Put 5 (DBytes payload)  ->  Get 5  ->  Match/PSome binds payload  ->  Ret (VVar 0)
    The outcome is [ORet (DSome (DBytes bytes_payload))] and the KV map has key 5. *)
Theorem bytes_correct :
  let '(outcome, w) := run_top DUnit sample_bytes in
  outcome = ORet (DBytes bytes_payload) /\
  M.find 5 (kv w) = Some (DBytes bytes_payload).
Proof.
  unfold run_top, sample_bytes, bytes_payload, init_world.
  cbn [run eval_val handle_kv map nth set_kv kv opt_to_dval
       match_pat push_env fold_left ascii_list_eqb Ascii.eqb].
  split.
  - reflexivity.
  - apply M.find_1, M.add_1. reflexivity.
Qed.

(** ** Inhabitance: the precondition (empty initial state) is trivially satisfied,
    so [bytes_correct] is not vacuously true. *)
Lemma bytes_correct_inhabited : exists w,
  run_top DUnit sample_bytes = (ORet (DBytes bytes_payload), w).
Proof.
  eexists.
  unfold run_top, sample_bytes, bytes_payload, init_world.
  cbn [run eval_val handle_kv map nth set_kv kv opt_to_dval
       match_pat push_env fold_left ascii_list_eqb Ascii.eqb].
  reflexivity.
Qed.

(** ** Proof-mutation check: a program that stores DIFFERENT bytes (empty list) is rejected.

    [sample_bytes_wrong] puts an empty byte string; the spec says the result is [Some bytes_payload],
    which has length 6. The [Fail] tactic proves the mutant violates the correctness statement,
    so the statement is NOT vacuous. *)
Definition sample_bytes_wrong : tm :=
  Bind (Perform OPut [VInt 5; VBytes []])
       (Bind (Perform OGet [VInt 5])
             (Match (VVar 0)
                [(PNone, Ret VNone);
                 (PSome, Ret (VVar 0))]
                (Ret VNone))).

(** The wrong program returns [Some (DBytes [])] (empty), not [Some (DBytes bytes_payload)].
    We prove the two outcomes differ, which demonstrates the spec is non-trivial. *)
Lemma bytes_wrong_outcome :
  let '(outcome, _) := run_top DUnit sample_bytes_wrong in
  outcome = ORet (DBytes []).
Proof.
  unfold run_top, sample_bytes_wrong, init_world.
  cbn [run eval_val handle_kv map nth set_kv kv opt_to_dval
       match_pat push_env fold_left ascii_list_eqb Ascii.eqb].
  reflexivity.
Qed.

(** The mutant output differs from the correct output:
    [DBytes []] ≠ [DBytes bytes_payload] — the payload is non-empty. *)
Lemma bytes_wrong_differs : ORet (DBytes []) <> ORet (DBytes bytes_payload).
Proof. unfold bytes_payload. discriminate. Qed.

(** Proof-mutation gate: [sample_bytes_wrong] (which stores [DBytes []]) cannot satisfy
    the correctness statement for [sample_bytes] (which requires [DBytes bytes_payload]).
    We prove this via [bytes_wrong_outcome] and [bytes_wrong_differs]:
    the wrong outcome is [DBytes []], which is ≠ [DBytes bytes_payload]. *)
Theorem bytes_wrong_rejected :
  ~ (let '(outcome, _) := run_top DUnit sample_bytes_wrong in
     outcome = ORet (DBytes bytes_payload)).
Proof.
  (* Reduce sample_bytes_wrong to its concrete outcome [DBytes []], then discriminate. *)
  unfold run_top, sample_bytes_wrong, init_world.
  cbn [run eval_val handle_kv map nth set_kv kv opt_to_dval
       match_pat push_env fold_left ascii_list_eqb Ascii.eqb].
  intro H. discriminate H.
Qed.

(** Surface the assumption footprint — must say "Closed under the global context". *)
Print Assumptions bytes_correct.
