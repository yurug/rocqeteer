(** * KV — Hoare layer, the [incr] correctness proof, and its anti-vacuity companions.

    Step 2 of the slice (kb/plan.md): prove the slice-1 program against the reference
    semantics, and prove the spec is NOT vacuous (an inhabitance lemma + a proof-mutation
    theorem). See kb/architecture/decisions/adr-0005-anti-vacuity.md and
    kb/spec/reference-semantics.md. *)

From Stdlib Require Import ZArith List FMapFacts FMapAVL OrderedTypeEx.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

(** Facts about the reference KV map (FMapAVL over Z). *)
Module Import KVFacts := FMapFacts.WFacts_fun(Z_as_OT)(M).

(** Put-then-get returns what was put (the state law "put k v ;; get k = Some v", P7). *)
Lemma find_add_same : forall k (v : dval) (s : state), M.find k (M.add k v s) = Some v.
Proof. intros; apply add_eq_o; reflexivity. Qed.

(** Put-then-put overwrites (the state law "put k v1 ;; put k v2 = put k v2", P7). *)
Lemma put_put : forall k (v1 v2 : dval) (s : state),
  M.Equal (M.add k v2 (M.add k v1 s)) (M.add k v2 s).
Proof.
  intros k v1 v2 s k'.
  destruct (Z.eq_dec k k') as [->|Hne].
  - rewrite !add_eq_o by reflexivity; reflexivity.
  - rewrite !add_neq_o by assumption; reflexivity.
Qed.

(** Get-then-get is idempotent: a read does not mutate the store, so a second read sees the
    same value and state (the state law "get k ;; get k = get k", P7's third law). *)
Lemma get_get : forall k (s : state),
  handle_kv OGet [DInt k] (snd (handle_kv OGet [DInt k] s)) = handle_kv OGet [DInt k] s.
Proof. reflexivity. Qed.

(** ** Hoare layer. A [Spec] is a precondition on the state and a postcondition relating
    the initial state, the result value, and the final state; [verifies] runs the closed
    term [t] from any [pre] state and demands [post]. *)
Record Spec : Type := {
  pre  : state -> Prop;
  post : state -> outcome -> state -> Prop;  (* result is now an outcome (value or error) *)
}.

Definition verifies (t : tm) (sp : Spec) : Prop :=
  forall s, pre sp s ->
    (* run from a world whose KV map is [s]; the spec constrains the final map [w'.(kv)]. *)
    let '(x, w') := run [] t (mkWorld s DUnit [] (M.empty dval)) in post sp s x w'.(kv).

(** The current integer counter at [k] (0 if absent or non-integer). *)
Definition cur (k : Z) (s : state) : Z :=
  match M.find k s with Some (DInt z) => z | _ => 0 end.

(** The slice-1 specification: from a store whose value at [k] is absent or an integer,
    [incr_at k] (1) leaves the counter at [k] equal to [succ] of its previous value, and
    (2) touches no other key (the FRAME clause — without it a clobbering impl would pass;
    see [incr_clobber_rejected] and audit finding 2). *)
Definition incr_spec (k : Z) : Spec := {|
  pre  := fun s => match M.find k s with
                   | None | Some (DInt _) => True
                   | Some _ => False
                   end;
  post := fun s _ s' =>
            M.find k s' = Some (DInt (Z.succ (cur k s)))
            /\ (forall k', k' <> k -> M.find k' s' = M.find k' s)
|}.

(** Keep the map operations as opaque constants so [cbn] reduces only the interpreter
    (run/eval_val/handle_kv/...) and never unfolds FMapAVL internals. *)
Opaque M.find M.add M.empty M.remove.

(** ** The correctness theorem: [incr_at k] meets [incr_spec k] (fully proved, QED). *)
Theorem incr_correct : forall k, verifies (incr_at k) (incr_spec k).
Proof.
  intros k s Hpre.
  unfold verifies, incr_at, incr_spec, cur in *.
  cbn [pre post run eval_val handle_kv map nth opt_to_dval set_kv kv] in Hpre |- *.
  destruct (M.find k s) as [d|] eqn:Hf.
  - (* present: pre forces d = DInt z; both write succ of the stored value *)
    destruct d as [| | z | | | | |]; try contradiction;
      cbn [run eval_val handle_kv map nth opt_to_dval set_kv kv];
      (split; [ rewrite find_add_same; reflexivity
              | intros k' Hk'; rewrite add_neq_o by congruence; reflexivity ]).
  - (* absent: counter starts at 0, becomes 1 = Z.succ 0 *)
    cbn [run eval_val handle_kv map nth opt_to_dval set_kv kv];
    (split; [ rewrite find_add_same; reflexivity
            | intros k' Hk'; rewrite add_neq_o by congruence; reflexivity ]).
Qed.

(** ** Anti-vacuity 1: the precondition is inhabited (the empty store satisfies it), so
    [incr_spec] is not vacuously true (kb/architecture/decisions/adr-0005-anti-vacuity.md). *)
Lemma incr_spec_inhabited : forall k, exists s, pre (incr_spec k) s.
Proof.
  intros k. exists (M.empty dval).
  cbn [pre incr_spec]. rewrite empty_o. exact I.
Qed.

(** ** Anti-vacuity 2 (proof-mutation): a wrong [incr] that writes 0 instead of [succ]
    does NOT satisfy the spec. This is the machine-checked mutant — if the spec were
    vacuous, this negation would be unprovable. *)
Definition incr_wrong (k : Z) : tm :=
  Bind (Perform OGet [VInt k])
       (MatchOpt (VVar 0)
          (Perform OPut [VInt k; VZero])
          (Perform OPut [VInt k; VZero])).

Theorem incr_wrong_rejected : ~ verifies (incr_wrong 0) (incr_spec 0).
Proof.
  intro Hv. unfold verifies, incr_wrong, incr_spec, cur in Hv.
  specialize (Hv (M.empty dval)).
  (* From the empty store the precondition holds, so the postcondition must hold too. *)
  cbn [pre post run eval_val handle_kv map nth opt_to_dval set_kv kv] in Hv.
  rewrite empty_o in Hv.
  cbn [run eval_val handle_kv map nth opt_to_dval set_kv kv] in Hv.
  specialize (Hv I).
  (* the wrong impl wrote 0, but the spec's value clause demands succ 0 = 1 *)
  destruct Hv as [Hval _].
  rewrite find_add_same in Hval.
  discriminate Hval.
Qed.

(** ** Anti-vacuity 3 (frame mutant): an [incr] that correctly increments [k] but also
    deletes a neighbouring key violates the FRAME clause of the spec. This proves the
    frame clause is load-bearing — without it, [incr_clobber] would pass (audit finding 2). *)
Definition incr_clobber (k : Z) : tm :=
  Bind (Perform OGet [VInt k])
       (MatchOpt (VVar 0)
          (Bind (Perform OPut [VInt k; VSucc VZero]) (Perform ODelete [VInt (k + 1)]))
          (Bind (Perform OPut [VInt k; VSucc (VVar 0)]) (Perform ODelete [VInt (k + 1)]))).

Theorem incr_clobber_rejected : ~ verifies (incr_clobber 0) (incr_spec 0).
Proof.
  intro Hv. unfold verifies, incr_clobber, incr_spec, cur in Hv.
  (* A store where the neighbour key 1 holds a value the clobber will wrongly delete. *)
  specialize (Hv (M.add 1 (DInt 5) (M.empty dval))).
  cbn [pre post run eval_val handle_kv map nth opt_to_dval set_kv kv] in Hv.
  (* find 0 (add 1 5 empty) = None, so the precondition holds. *)
  rewrite add_neq_o in Hv by congruence. rewrite empty_o in Hv.
  cbn [run eval_val handle_kv map nth opt_to_dval set_kv kv] in Hv.
  specialize (Hv I).
  destruct Hv as [_ Hframe].
  (* the frame says key 1 is untouched, but the clobber deleted it *)
  specialize (Hframe 1 ltac:(congruence)).
  (* LHS: key 1 was deleted -> None; RHS: key 1 originally held 5 *)
  rewrite remove_eq_o in Hframe by reflexivity.
  rewrite find_add_same in Hframe.
  discriminate Hframe.
Qed.

(** Surface the assumption footprint of the correctness theorem for the TCB report. *)
Print Assumptions incr_correct.
