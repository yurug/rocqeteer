(** * KV — Hoare layer, the [incr] correctness proof, and its anti-vacuity companions.

    Step 2 of the slice (kb/plan.md): prove the slice-1 program against the reference
    semantics, and prove the spec is NOT vacuous (an inhabitance lemma + a proof-mutation
    theorem). See kb/architecture/decisions/adr-0005-anti-vacuity.md and
    kb/spec/reference-semantics.md.

    R4 (adr-0011-time-and-expiring-store): re-proven over the expiring bytes-keyed store.
    Keys are byte strings; the spec reads the LIVE view ([find_live]) so the theorem holds
    for EVERY instant [now] and for stores that carry deadlines — deadline-less behavior
    is exactly the old KV behavior, and the [put] clause additionally pins that OPut
    CLEARS any pre-existing deadline (the stored entry is [(…, None)]). *)

From Stdlib Require Import ZArith List FMapFacts FMapAVL OrderedTypeEx String Ascii.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

(** Facts about the reference store map (FMapAVL over String_as_OT). *)
Module Import KVFacts := FMapFacts.WFacts_fun(String_as_OT)(M).

(** Put-then-get returns what was put (the state law "put k v ;; get k = Some v", P7). *)
Lemma find_add_same : forall k (v : entry) (s : state), M.find k (M.add k v s) = Some v.
Proof. intros; apply add_eq_o; reflexivity. Qed.

(** Put-then-put overwrites (the state law "put k v1 ;; put k v2 = put k v2", P7). *)
Lemma put_put : forall k (v1 v2 : entry) (s : state),
  M.Equal (M.add k v2 (M.add k v1 s)) (M.add k v2 s).
Proof.
  intros k v1 v2 s k'.
  destruct (string_dec k k') as [->|Hne].
  - rewrite !add_eq_o by reflexivity; reflexivity.
  - rewrite !add_neq_o by assumption; reflexivity.
Qed.

(** Get-then-get is idempotent: a read does not mutate the store, so a second read sees the
    same value and state (the state law "get k ;; get k = get k", P7's third law) — at any
    instant [now], deadlines included. *)
Lemma get_get : forall now kb (s : state),
  handle_store now OGet [DBytes kb] (snd (handle_store now OGet [DBytes kb] s))
  = handle_store now OGet [DBytes kb] s.
Proof. reflexivity. Qed.

(** ** Hoare layer. A [Spec] is a precondition on the state and a postcondition relating
    the initial state, the result value, and the final state; [verifies] runs the closed
    term [t] from any [pre] state AT INSTANT [now] and demands [post]. *)
Record Spec : Type := {
  pre  : state -> Prop;
  post : state -> outcome -> state -> Prop;  (* result is now an outcome (value or error) *)
}.

Definition verifies (now : Z) (t : tm) (sp : Spec) : Prop :=
  forall s, pre sp s ->
    (* run from a world whose store is [s] at instant [now]; the spec constrains the
       final map [w'.(kv)]. *)
    let '(x, w') := run [] t (mkWorld s DUnit now [] (M.empty dval) [] (M.empty (list ascii)) [] 3) in post sp s x w'.(kv).

(** The current integer counter at [k], read through the LIVE view (0 if absent, expired,
    or non-integer). *)
Definition cur (now : Z) (k : string) (s : state) : Z :=
  match find_live now k s with Some (DInt z, _) => z | _ => 0 end.

(** The slice-1 specification: from a store whose LIVE value at [k] is absent or an
    integer, [incr_at kb] (1) leaves the entry at [k] equal to [succ] of its previous
    live value WITH NO DEADLINE (OPut clears it), and (2) touches no other key (the FRAME
    clause — without it a clobbering impl would pass; see [incr_clobber_rejected]). *)
Definition incr_spec (now : Z) (k : string) : Spec := {|
  pre  := fun s => match find_live now k s with
                   | None | Some (DInt _, _) => True
                   | Some _ => False
                   end;
  post := fun s _ s' =>
            M.find k s' = Some (DInt (Z.succ (cur now k s)), None)
            /\ (forall k', k' <> k -> M.find k' s' = M.find k' s)
|}.

(** Keep the map operations as opaque constants so [cbn] reduces only the interpreter
    (run/eval_val/handle_store/...) and never unfolds FMapAVL internals. *)
Opaque M.find M.add M.empty M.remove.

(** ** The correctness theorem: [incr_at kb] meets [incr_spec now (key of kb)] for EVERY
    instant [now] and every byte-string key [kb] (fully proved, QED). *)
Theorem incr_correct : forall now kb,
  verifies now (incr_at kb) (incr_spec now (string_of_list_ascii kb)).
Proof.
  intros now kb s Hpre.
  unfold verifies, incr_at, incr_spec, cur in *.
  cbn [pre post run eval_val handle_store map nth opt_to_dval set_kv kv now_ms
       match_pat push_env fold_left] in Hpre |- *.
  destruct (find_live now (string_of_list_ascii kb) s) as [[d dl]|] eqn:Hf.
  - (* live: pre forces d = DInt z; both write succ of the stored value, deadline cleared *)
    destruct d as [| | z | | | | | | |]; try contradiction;
      cbn [run eval_val handle_store map nth opt_to_dval set_kv kv now_ms
           match_pat push_env fold_left];
      (split; [ rewrite find_add_same; reflexivity
              | intros k' Hk'; rewrite add_neq_o by congruence; reflexivity ]).
  - (* absent (or expired): counter starts at 0, becomes 1 = Z.succ 0 *)
    cbn [run eval_val handle_store map nth opt_to_dval set_kv kv now_ms
         match_pat push_env fold_left];
    (split; [ rewrite find_add_same; reflexivity
            | intros k' Hk'; rewrite add_neq_o by congruence; reflexivity ]).
Qed.

(** ** Anti-vacuity 1: the precondition is inhabited (the empty store satisfies it), so
    [incr_spec] is not vacuously true (kb/architecture/decisions/adr-0005-anti-vacuity.md). *)
Lemma incr_spec_inhabited : forall now k, exists s, pre (incr_spec now k) s.
Proof.
  intros now k. exists (M.empty entry).
  cbn [pre incr_spec]. unfold find_live. rewrite empty_o. exact I.
Qed.

(** A DEADLINE-CARRYING inhabitant too: a store where [k] holds an integer with a live
    deadline also satisfies the precondition — so [incr_correct] genuinely covers stores
    with expiry metadata, not only the deadline-less fragment (adr-0011 anti-vacuity). *)
Lemma incr_spec_inhabited_deadline : forall k,
  exists s, pre (incr_spec 500 k) s /\ M.find k s = Some (DInt 5, Some 500).
Proof.
  intros k. exists (M.add k (DInt 5, Some 500) (M.empty entry)).
  split.
  - cbn [pre incr_spec]. unfold find_live.
    rewrite find_add_same. cbn [live snd].
    assert (H : (500 <=? 500) = true) by reflexivity. rewrite H. exact I.
  - apply find_add_same.
Qed.

(** ** Anti-vacuity 2 (proof-mutation): a wrong [incr] that writes 0 instead of [succ]
    does NOT satisfy the spec. This is the machine-checked mutant — if the spec were
    vacuous, this negation would be unprovable. *)
Definition incr_wrong (k : list ascii) : tm :=
  Bind (Perform OGet [VBytes k])
       (Match (VVar 0)
          [(PNone, Perform OPut [VBytes k; VZero]);
           (PSome, Perform OPut [VBytes k; VZero])]
          (Perform OPut [VBytes k; VZero])).

Definition kb0 : list ascii := list_ascii_of_string "0".

Theorem incr_wrong_rejected :
  ~ verifies 0 (incr_wrong kb0) (incr_spec 0 (string_of_list_ascii kb0)).
Proof.
  intro Hv. unfold verifies, incr_wrong, incr_spec, cur in Hv.
  specialize (Hv (M.empty entry)).
  (* From the empty store the precondition holds, so the postcondition must hold too. *)
  cbn [pre post run eval_val handle_store map nth opt_to_dval set_kv kv now_ms
       match_pat push_env fold_left] in Hv.
  unfold find_live in Hv. rewrite empty_o in Hv.
  cbn [run eval_val handle_store map nth opt_to_dval set_kv kv now_ms
       match_pat push_env fold_left] in Hv.
  specialize (Hv I).
  (* the wrong impl wrote 0, but the spec's value clause demands succ 0 = 1 *)
  destruct Hv as [Hval _].
  rewrite find_add_same in Hval.
  discriminate Hval.
Qed.

(** ** Anti-vacuity 3 (frame mutant): an [incr] that correctly increments [k] but also
    deletes a neighbouring key violates the FRAME clause of the spec. This proves the
    frame clause is load-bearing — without it, [incr_clobber] would pass (audit finding 2). *)
Definition kb1 : list ascii := list_ascii_of_string "1".

Definition incr_clobber (k : list ascii) : tm :=
  Bind (Perform OGet [VBytes k])
       (Match (VVar 0)
          [(PNone, Bind (Perform OPut [VBytes k; VSucc VZero]) (Perform ODelete [VBytes kb1]));
           (PSome, Bind (Perform OPut [VBytes k; VSucc (VVar 0)]) (Perform ODelete [VBytes kb1]))]
          (Bind (Perform OPut [VBytes k; VSucc VZero]) (Perform ODelete [VBytes kb1]))).

Theorem incr_clobber_rejected :
  ~ verifies 0 (incr_clobber kb0) (incr_spec 0 (string_of_list_ascii kb0)).
Proof.
  intro Hv. unfold verifies, incr_clobber, incr_spec, cur in Hv.
  (* A store where the neighbour key "1" holds a value the clobber will wrongly delete. *)
  specialize (Hv (M.add (string_of_list_ascii kb1) (DInt 5, None) (M.empty entry))).
  cbn [pre post run eval_val handle_store map nth opt_to_dval set_kv kv now_ms
       match_pat push_env fold_left] in Hv.
  (* find_live "0" (add "1" … empty) = None, so the precondition holds. *)
  unfold find_live in Hv.
  rewrite add_neq_o in Hv by (vm_compute; congruence). rewrite empty_o in Hv.
  cbn [run eval_val handle_store map nth opt_to_dval set_kv kv now_ms
       match_pat push_env fold_left] in Hv.
  specialize (Hv I).
  destruct Hv as [_ Hframe].
  (* the frame says key "1" is untouched, but the clobber deleted it *)
  specialize (Hframe (string_of_list_ascii kb1) ltac:(vm_compute; congruence)).
  (* LHS: key "1" was deleted -> None; RHS: key "1" originally held 5 *)
  rewrite remove_eq_o in Hframe by reflexivity.
  rewrite find_add_same in Hframe.
  discriminate Hframe.
Qed.

(** Surface the assumption footprint of the correctness theorem for the TCB report. *)
Print Assumptions incr_correct.
