(** * Recursion — the bounded loop [Repeat], proven correct by induction on the fuel.

    [Repeat n body] runs [body] [n] times. This file proves a loop invariant by induction:
    incrementing key 0 [n] times adds [n] to it; hence [sample_count] (5 increments from
    empty) leaves key 0 = 5. This is the first proof that reasons about RECURSION, not just a
    fixed-shape program (kb/spec/effir.md recursion). *)

From Stdlib Require Import ZArith List Lia FMapFacts FMapAVL OrderedTypeEx.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

Module Import RFacts := FMapFacts.WFacts_fun(Z_as_OT)(M).
Opaque M.find M.add M.empty M.remove.

Lemma find_add_same : forall k (v : dval) (s : state), M.find k (M.add k v s) = Some v.
Proof. intros; apply add_eq_o; reflexivity. Qed.

(** One-step unfold of the loop, and the empty loop — both hold definitionally. *)
Lemma repeat_step : forall env m body w,
  run env (Repeat (S m) body) w =
  match run env body w with
  | (ORet _, w1) => run env (Repeat m body) w1
  | (OErr e, w1) => (OErr e, w1)
  end.
Proof. reflexivity. Qed.

Lemma repeat_zero : forall env body w, run env (Repeat 0 body) w = (ORet DUnit, w).
Proof. reflexivity. Qed.

(** One increment of key 0: present case (value [c]) and absent case (starts at 0). *)
Lemma incr0_present : forall c w,
  M.find 0 w.(kv) = Some (DInt c) ->
  let '(o, w') := run [] (incr_at 0) w in
  o = ORet DUnit /\ M.find 0 w'.(kv) = Some (DInt (Z.succ c)).
Proof.
  intros c w H. unfold incr_at.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv kv
       match_pat push_env fold_left].
  rewrite H.
  cbn [opt_to_dval run eval_val map nth handle_kv set_kv kv
       match_pat push_env fold_left].
  split; [ reflexivity | apply find_add_same ].
Qed.

Lemma incr0_absent : forall w,
  M.find 0 w.(kv) = None ->
  let '(o, w') := run [] (incr_at 0) w in
  o = ORet DUnit /\ M.find 0 w'.(kv) = Some (DInt 1).
Proof.
  intros w H. unfold incr_at.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv kv
       match_pat push_env fold_left].
  rewrite H.
  cbn [opt_to_dval run eval_val map nth handle_kv set_kv kv
       match_pat push_env fold_left].
  split; [ reflexivity | apply find_add_same ].
Qed.

(** Loop invariant: from a world where key 0 = [c], [n] increments leave key 0 = c + n. *)
Lemma repeat_incr_present : forall n c w,
  M.find 0 w.(kv) = Some (DInt c) ->
  M.find 0 (snd (run [] (Repeat n (incr_at 0)) w)).(kv) = Some (DInt (c + Z.of_nat n)).
Proof.
  induction n as [| n IH]; intros c w H.
  - rewrite repeat_zero. cbn [snd]. rewrite H. f_equal; f_equal; lia.
  - rewrite repeat_step.
    pose proof (incr0_present c w H) as Hstep.
    destruct (run [] (incr_at 0) w) as [o w1].
    destruct Hstep as [-> Hw1].
    rewrite (IH (Z.succ c) w1 Hw1). f_equal; f_equal; lia.
Qed.

(** [sample_count] = increment key 0 five times from empty; key 0 ends at 5. *)
Theorem sample_count_correct :
  M.find 0 (snd (run [] sample_count (init_world DUnit))).(kv) = Some (DInt 5).
Proof.
  unfold sample_count. rewrite repeat_step.
  assert (Hempty : M.find 0 (init_world DUnit).(kv) = None)
    by (cbn [init_world kv]; apply empty_o).
  pose proof (incr0_absent (init_world DUnit) Hempty) as Hstep.
  destruct (run [] (incr_at 0) (init_world DUnit)) as [o w1].
  destruct Hstep as [-> Hw1].
  rewrite (repeat_incr_present 4 1 w1 Hw1). f_equal; f_equal; lia.
Qed.

Print Assumptions sample_count_correct.
