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

(** ** Hoare layer. A [Spec] is a precondition on the state and a postcondition relating
    the initial state, the result value, and the final state; [verifies] runs the closed
    term [t] from any [pre] state and demands [post]. *)
Record Spec : Type := {
  pre  : state -> Prop;
  post : state -> dval -> state -> Prop;
}.

Definition verifies (t : tm) (sp : Spec) : Prop :=
  forall s, pre sp s ->
    let '(x, s') := run [] t s in post sp s x s'.

(** The current integer counter at [k] (0 if absent or non-integer). *)
Definition cur (k : Z) (s : state) : Z :=
  match M.find k s with Some (DInt z) => z | _ => 0 end.

(** The slice-1 specification: from a store whose value at [k] is absent or an integer,
    [incr_at k] leaves the counter at [k] equal to [succ] of its previous value. *)
Definition incr_spec (k : Z) : Spec := {|
  pre  := fun s => match M.find k s with
                   | None | Some (DInt _) => True
                   | Some _ => False
                   end;
  post := fun s _ s' => M.find k s' = Some (DInt (Z.succ (cur k s)))
|}.

(** Keep the map operations as opaque constants so [cbn] reduces only the interpreter
    (run/eval_val/handle/...) and never unfolds FMapAVL internals. *)
Opaque M.find M.add M.empty M.remove.

(** ** The correctness theorem: [incr_at k] meets [incr_spec k] (fully proved, QED). *)
Theorem incr_correct : forall k, verifies (incr_at k) (incr_spec k).
Proof.
  intros k s Hpre.
  unfold verifies, incr_at, incr_spec, cur in *.
  cbn [pre post run eval_val handle map nth opt_to_dval] in Hpre |- *.
  destruct (M.find k s) as [d|] eqn:Hf.
  - (* present: pre forces d = DInt z; both write succ of the stored value *)
    destruct d as [| | z | | | |]; try contradiction;
      cbn [run eval_val handle map nth opt_to_dval];
      rewrite find_add_same; reflexivity.
  - (* absent: counter starts at 0, becomes 1 = Z.succ 0 *)
    cbn [run eval_val handle map nth opt_to_dval];
    rewrite find_add_same; reflexivity.
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
  cbn [pre post run eval_val handle map nth opt_to_dval] in Hv.
  rewrite empty_o in Hv.
  cbn [run eval_val handle map nth opt_to_dval] in Hv.
  specialize (Hv I).
  (* the wrong impl wrote 0, but the spec demands succ 0 = 1 *)
  rewrite find_add_same in Hv.
  discriminate Hv.
Qed.

(** Surface the assumption footprint of the correctness theorem for the TCB report. *)
Print Assumptions incr_correct.
