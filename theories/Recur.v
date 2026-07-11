(** * Recursion — the bounded loop [Repeat], proven correct by induction on the fuel.

    [Repeat n body] runs [body] [n] times. This file proves a loop invariant by induction:
    incrementing key "0" [n] times adds [n] to it; hence [sample_count] (5 increments from
    empty) leaves key "0" = 5. This is the first proof that reasons about RECURSION, not
    just a fixed-shape program (kb/spec/effir.md recursion).

    R4 (adr-0011): keys are byte strings; entries carry (value, optional deadline). The
    invariant is stated over deadline-less entries — [incr_at] only ever writes
    [(…, None)] (OPut clears deadlines), so the invariant is preserved for any instant. *)

From Stdlib Require Import ZArith List Lia FMapFacts FMapAVL OrderedTypeEx String Ascii.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

Module Import RFacts := FMapFacts.WFacts_fun(String_as_OT)(M).
Opaque M.find M.add M.empty M.remove.

Lemma find_add_same : forall k (v : entry) (s : state), M.find k (M.add k v s) = Some v.
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

(** One increment of key "0": present case (deadline-less value [c]) and absent case
    (starts at 0). *)
Lemma incr0_present : forall c w,
  M.find (string_of_list_ascii key0) w.(kv) = Some (DInt c, None) ->
  let '(o, w') := run [] (incr_at key0) w in
  o = ORet DUnit
  /\ M.find (string_of_list_ascii key0) w'.(kv) = Some (DInt (Z.succ c), None).
Proof.
  intros c w H. unfold incr_at.
  cbn [run eval_val map nth opt_to_dval handle_store set_kv kv now_ms
       match_pat push_env fold_left].
  unfold find_live. rewrite H.
  cbn [live snd run eval_val map nth opt_to_dval handle_store set_kv kv now_ms
       match_pat push_env fold_left].
  split; [ reflexivity | apply find_add_same ].
Qed.

Lemma incr0_absent : forall w,
  M.find (string_of_list_ascii key0) w.(kv) = None ->
  let '(o, w') := run [] (incr_at key0) w in
  o = ORet DUnit
  /\ M.find (string_of_list_ascii key0) w'.(kv) = Some (DInt 1, None).
Proof.
  intros w H. unfold incr_at.
  cbn [run eval_val map nth opt_to_dval handle_store set_kv kv now_ms
       match_pat push_env fold_left].
  unfold find_live. rewrite H.
  cbn [run eval_val map nth opt_to_dval handle_store set_kv kv now_ms
       match_pat push_env fold_left].
  split; [ reflexivity | apply find_add_same ].
Qed.

(** Loop invariant: from a world where key "0" = [c] (deadline-less), [n] increments leave
    key "0" = c + n (still deadline-less). *)
Lemma repeat_incr_present : forall n c w,
  M.find (string_of_list_ascii key0) w.(kv) = Some (DInt c, None) ->
  M.find (string_of_list_ascii key0) (snd (run [] (Repeat n (incr_at key0)) w)).(kv)
  = Some (DInt (c + Z.of_nat n), None).
Proof.
  induction n as [| n IH]; intros c w H.
  - rewrite repeat_zero. cbn [snd]. rewrite H. do 3 f_equal; lia.
  - rewrite repeat_step.
    pose proof (incr0_present c w H) as Hstep.
    destruct (run [] (incr_at key0) w) as [o w1].
    destruct Hstep as [-> Hw1].
    rewrite (IH (Z.succ c) w1 Hw1). do 3 f_equal; lia.
Qed.

(** [sample_count] = increment key "0" five times from empty; key "0" ends at 5 —
    at EVERY instant [now]. *)
Theorem sample_count_correct : forall now,
  M.find (string_of_list_ascii key0)
    (snd (run [] sample_count (init_world DUnit now))).(kv) = Some (DInt 5, None).
Proof.
  intro now. unfold sample_count. rewrite repeat_step.
  assert (Hempty : M.find (string_of_list_ascii key0) (init_world DUnit now).(kv) = None)
    by (cbn [init_world kv]; apply empty_o).
  pose proof (incr0_absent (init_world DUnit now) Hempty) as Hstep.
  destruct (run [] (incr_at key0) (init_world DUnit now)) as [o w1].
  destruct Hstep as [-> Hw1].
  rewrite (repeat_incr_present 4 1 w1 Hw1). reflexivity.
Qed.

Print Assumptions sample_count_correct.
