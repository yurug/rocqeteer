(** * Error effect — the short-circuit (abort) law, proven, with anti-vacuity.

    [OThrow] aborts the computation: its continuation never runs, and the state is whatever
    was committed before the throw. This file proves the algebraic law "throw e ;; k = throw
    e" (kb/spec/reference-semantics.md §laws) and a concrete abort, plus a mutant showing the
    throw is what causes the abort. The OCaml runtime (runtime/err.ml) is asserted to refine
    this and validated by tests/diff_err.ml.

    R4 (adr-0011): keys are byte strings; store entries carry (value, optional deadline). *)

From Stdlib Require Import ZArith List String Ascii.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Algebraic law: throwing aborts the bind — the continuation [k] is discarded and the
    state [s] is unchanged, for ANY error expression [e] and continuation [k]
    (the report's "throw e >>= k = throw e"). *)
Lemma throw_aborts : forall env e k w,
  run env (Bind (Perform OThrow [e]) k) w = (OErr (eval_val env e), w).
Proof. intros; cbn [run eval_val map nth]; reflexivity. Qed.

(** ** Concrete abort: [sample_throw] = put "1"; throw 99; put "2". The outcome is the
    error, the pre-throw write to key "1" committed (deadline-less entry), and the
    post-throw write to key "2" never happened. *)
Theorem sample_throw_aborts :
  let '(o, w') := run [] sample_throw (init_world DUnit 0) in
  o = OErr (DInt 99)
  /\ M.find (string_of_list_ascii key1) w'.(kv) = Some (DInt 1, None)
  /\ M.find (string_of_list_ascii key2) w'.(kv) = None.
Proof. vm_compute. repeat split. Qed.

(** ** Anti-vacuity (mutant): replace the throw with [Ret] and the computation COMPLETES —
    outcome [ORet], and key "2" IS written. So the abort in [sample_throw_aborts] is caused
    by the throw, not by anything else (kb/architecture/decisions/adr-0005-anti-vacuity.md). *)
Definition sample_nothrow : tm :=
  Bind (Perform OPut [VBytes key1; VSucc VZero])
       (Bind (Ret VUnit)
             (Perform OPut [VBytes key2; VSucc (VSucc VZero)])).

Theorem sample_nothrow_completes :
  let '(o, w') := run [] sample_nothrow (init_world DUnit 0) in
  o = ORet DUnit /\ M.find (string_of_list_ascii key2) w'.(kv) = Some (DInt 2, None).
Proof. vm_compute. repeat split. Qed.

Print Assumptions sample_throw_aborts.
