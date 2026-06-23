(** * Env effect — the read-only-context laws, proven, with anti-vacuity.

    [OAsk] reads the ambient context and changes nothing. This file proves [ask] reads the
    context, the idempotence law "ask ;; ask = ask" (kb/spec/reference-semantics.md §laws),
    a concrete program where the asked value lands in the store, and a mutant that ignores
    the context. The OCaml handler (runtime/env.ml) refines this, validated by
    tests/diff_env.ml. *)

From Stdlib Require Import ZArith List FMapFacts FMapAVL OrderedTypeEx.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

Module Import EnvFacts := FMapFacts.WFacts_fun(Z_as_OT)(M).
Opaque M.find M.add M.empty M.remove.

Lemma find_add_same : forall k (v : dval) (s : state), M.find k (M.add k v s) = Some v.
Proof. intros; apply add_eq_o; reflexivity. Qed.

(** [ask] returns the context and leaves the state unchanged. *)
Lemma ask_reads_ctx : forall env w,
  run env (Perform OAsk []) w = (ORet w.(ctx), w).
Proof. intros; reflexivity. Qed.

(** Idempotence: "ask ;; ask = ask" — reading twice yields the same context and state. *)
Lemma ask_ask : forall env w,
  run env (Bind (Perform OAsk []) (Perform OAsk [])) w = (ORet w.(ctx), w).
Proof. intros; reflexivity. Qed.

(** Concrete: [sample_env] = ask; put 1 := asked value. Key 1 ends up holding the context. *)
Theorem sample_env_lands : forall c,
  let '(o, w') := run [] sample_env (init_world (DInt c)) in
  o = ORet DUnit /\ M.find 1 w'.(kv) = Some (DInt c).
Proof.
  intro c. unfold sample_env.
  cbn [run eval_val handle_kv map nth opt_to_dval set_kv kv].
  split; [ reflexivity | rewrite find_add_same; reflexivity ].
Qed.

(** Anti-vacuity (mutant): a program that asks but stores 0 instead of the asked value
    does NOT land the context — so [sample_env_lands]'s "key 1 = ctx" clause is load-bearing. *)
Definition sample_env_wrong : tm :=
  Bind (Perform OAsk []) (Perform OPut [VInt 1; VZero]).

Theorem sample_env_wrong_ignores_ctx : forall c, c <> 0 ->
  let '(_, w') := run [] sample_env_wrong (init_world (DInt c)) in
  M.find 1 w'.(kv) <> Some (DInt c).
Proof.
  intros c Hc. unfold sample_env_wrong.
  cbn [run eval_val handle_kv map nth opt_to_dval set_kv kv].
  rewrite find_add_same. congruence.
Qed.

Print Assumptions sample_env_lands.
