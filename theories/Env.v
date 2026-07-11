(** * Env effect — the read-only-context laws, proven, with anti-vacuity.

    [OAsk] reads the ambient context and changes nothing. This file proves [ask] reads the
    context, the idempotence law "ask ;; ask = ask" (kb/spec/reference-semantics.md §laws),
    a concrete program where the asked value lands in the store, and a mutant that ignores
    the context. The OCaml handler (runtime/env.ml) refines this, validated by
    tests/diff_env.ml.

    R4 (adr-0011): keys are byte strings; store entries carry (value, optional deadline). *)

From Stdlib Require Import ZArith List String Ascii.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

(** [ask] returns the context and leaves the state unchanged. *)
Lemma ask_reads_ctx : forall env w,
  run env (Perform OAsk []) w = (ORet w.(ctx), w).
Proof. intros; reflexivity. Qed.

(** Idempotence: "ask ;; ask = ask" — reading twice yields the same context and state. *)
Lemma ask_ask : forall env w,
  run env (Bind (Perform OAsk []) (Perform OAsk [])) w = (ORet w.(ctx), w).
Proof. intros; reflexivity. Qed.

(** Concrete: [sample_env] = ask; put "1" := asked value. Key "1" ends up holding the
    context (deadline-less), at every instant [now] and for every context [c]. *)
Theorem sample_env_lands : forall c now,
  let '(o, w') := run [] sample_env (init_world (DInt c) now) in
  o = ORet DUnit /\ M.find (string_of_list_ascii key1) w'.(kv) = Some (DInt c, None).
Proof. intros c now. vm_compute. repeat split. Qed.

(** Anti-vacuity (mutant): a program that asks but stores 0 instead of the asked value
    does NOT land the context — so [sample_env_lands]'s "key 1 = ctx" clause is load-bearing. *)
Definition sample_env_wrong : tm :=
  Bind (Perform OAsk []) (Perform OPut [VBytes key1; VZero]).

Theorem sample_env_wrong_ignores_ctx : forall c, c <> 0 ->
  let '(_, w') := run [] sample_env_wrong (init_world (DInt c) 0) in
  M.find (string_of_list_ascii key1) w'.(kv) <> Some (DInt c, None).
Proof. intros c Hc. vm_compute. injection 1. congruence. Qed.

Print Assumptions sample_env_lands.
