(** * Error effect — the short-circuit (abort) law, proven, with anti-vacuity.

    [OThrow] aborts the computation: its continuation never runs, and the state is whatever
    was committed before the throw. This file proves the algebraic law "throw e ;; k = throw
    e" (kb/spec/reference-semantics.md §laws) and a concrete abort, plus a mutant showing the
    throw is what causes the abort. The OCaml runtime (runtime/err.ml) is asserted to refine
    this and validated by tests/diff_err.ml. *)

From Stdlib Require Import ZArith List FMapFacts FMapAVL OrderedTypeEx.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

Module Import EFacts := FMapFacts.WFacts_fun(Z_as_OT)(M).
Opaque M.find M.add M.empty M.remove.

Lemma find_add_same : forall k (v : dval) (s : state), M.find k (M.add k v s) = Some v.
Proof. intros; apply add_eq_o; reflexivity. Qed.

(** ** Algebraic law: throwing aborts the bind — the continuation [k] is discarded and the
    state [s] is unchanged, for ANY error expression [e] and continuation [k]
    (the report's "throw e >>= k = throw e"). *)
Lemma throw_aborts : forall env e k s,
  run env (Bind (Perform OThrow [e]) k) s = (OErr (eval_val env e), s).
Proof. intros; cbn [run eval_val nth]; reflexivity. Qed.

(** ** Concrete abort: [sample_throw] = put 1; throw 99; put 2. The outcome is the error,
    the pre-throw write to key 1 committed, and the post-throw write to key 2 never happened. *)
Theorem sample_throw_aborts :
  let '(o, s') := run [] sample_throw (M.empty dval) in
  o = OErr (DInt 99)
  /\ M.find 1 s' = Some (DInt 1)
  /\ M.find 2 s' = None.
Proof.
  unfold sample_throw.
  cbn [run eval_val handle map nth opt_to_dval].
  split; [ reflexivity | split ].
  - rewrite find_add_same; reflexivity.
  - rewrite add_neq_o by congruence; rewrite empty_o; reflexivity.
Qed.

(** ** Anti-vacuity (mutant): replace the throw with [Ret] and the computation COMPLETES —
    outcome [ORet], and key 2 IS written. So the abort in [sample_throw_aborts] is caused by
    the throw, not by anything else (kb/architecture/decisions/adr-0005-anti-vacuity.md). *)
Definition sample_nothrow : tm :=
  Bind (Perform OPut [VInt 1; VSucc VZero])
       (Bind (Ret VUnit)
             (Perform OPut [VInt 2; VSucc (VSucc VZero)])).

Theorem sample_nothrow_completes :
  let '(o, s') := run [] sample_nothrow (M.empty dval) in
  o = ORet DUnit /\ M.find 2 s' = Some (DInt 2).
Proof.
  unfold sample_nothrow.
  cbn [run eval_val handle map nth opt_to_dval].
  split; [ reflexivity | rewrite find_add_same; reflexivity ].
Qed.

Print Assumptions sample_throw_aborts.
