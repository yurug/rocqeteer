(** * LogicDemo — R14 ACCEPTANCE GATE (adr-0015 §implementers, Phase A).

    Two ∀-QUANTIFIED end-to-end program theorems proven with the Logic.v rule library
    and the LogicTactics.v tactics — the theorem-quality ceiling moving from
    adversarially-placed instances to "∀ keys, values, deadlines, instants":

    1. GENERAL GET ([get_general]): for EVERY key, value, optional deadline, world
       (hence every store and every instant), over any store where the key is
       physically bound, the program [Bind (Perform OGet [VBytes k]) (Ret (VVar 0))]
       returns DSome v iff the binding is live at world.now_ms (DNone if expired) and
       leaves the world LITERALLY unchanged. "Store unchanged" is stated as the
       strongest provable form — final world = initial world, w' = w — because OGet's
       world update is [set_kv w (kv w)], which IS w by record eta ([set_kv_id]);
       this subsumes both the M.elements formulation and maps_to-preservation.

    2. GENERAL PUT-CLEARS-DEADLINE ([put_general]): for EVERY key, value expression
       and world, after [Perform OPut [VBytes k; vv]] the store binds k to
       (eval vv, None) — deadline CLEARED — and EVERY other key's physical binding is
       untouched (the ∀ k' <> k frame clause: the de-facto frame lemma for the keyed
       store), with all non-kv world fields unchanged.

    Anti-vacuity (house invariant 4 + adr-0015 §Decision 5):
    - Inhabitance: explicit witnesses built from the SAME concrete instance
      TimeStore.v's corpus already exercises ([deadline_state_inhabited] /
      [alive_at_deadline]'s store shape: key "a" -> (DInt 7, deadline 1000)), at both
      boundary sides (now = dl and now = dl + 1).
    - MUTANT: the general GET spec is proven FALSE under TimeStore.v's [run_mut]
      (the <-liveness mutant) at the boundary instant now = dl
      ([get_general_falsified_under_mutant]) — the spec has teeth exactly at the
      oracle-validated boundary.
    - The vm_compute instance corpus stays authoritative: concrete corollaries below
      re-derive corpus-shaped facts BOTH by vm_compute and from the general theorems.

    All vm_compute uses are on CLOSED terms only (theories/Prims.v header). *)

From Stdlib Require Import ZArith List String Ascii Bool Lia.
From Rocqeteer Require Import EffIR Samples StoreAssert Logic LogicTactics TimeStore.
Import ListNotations.
Local Open Scope Z_scope.

(* ===== §1  The two programs ================================================ *)

(** General GET: read a key, return the result (the adr-0015 suggested shape). *)
Definition get_prog (kbytes : list ascii) : tm :=
  Bind (Perform OGet [VBytes kbytes]) (Ret (VVar 0)).

(** General PUT: store a value expression at a key (OPut clears any deadline). *)
Definition put_prog (kbytes : list ascii) (vv : val) : tm :=
  Perform OPut [VBytes kbytes; vv].

(* ===== §2  ACCEPTANCE THEOREM (a): general GET ============================= *)

(** wp form, proven with the rule library (wp_bind -> wp_get -> wp_ret). *)
Theorem get_general_wp :
  forall (env : list dval) (kbytes : list ascii) (v : dval) (dl : option Z)
         (w : world),
    maps_to (string_of_list_ascii kbytes) v dl (kv w) ->
    wp env (get_prog kbytes)
       (fun o w' =>
          o = ORet (if live (now_ms w) (v, dl) then DSome v else DNone)
          /\ w' = w) w.
Proof.
  intros env kbytes v dl w Hm; unfold get_prog.
  wp_step. wp_step.
  rewrite (find_live_maps_to (now_ms w) _ _ _ _ Hm).
  destruct (live (now_ms w) (v, dl)); wp_auto.
Qed.

(** Run form (adequacy unfolded): a wp theorem IS a run theorem. *)
Theorem get_general :
  forall env kbytes v dl w,
    maps_to (string_of_list_ascii kbytes) v dl (kv w) ->
    run env (get_prog kbytes) w
    = (ORet (if live (now_ms w) (v, dl) then DSome v else DNone), w).
Proof.
  intros env kbytes v dl w Hm.
  pose proof (get_general_wp env kbytes v dl w Hm) as W; unfold wp in W.
  revert W; destruct (run env (get_prog kbytes) w) as [o w']; intro W.
  destruct W as [-> ->]; reflexivity.
Qed.

(** The two named faces of the boundary. *)
Corollary get_general_live_case :
  forall env kbytes v dl w,
    maps_to (string_of_list_ascii kbytes) v dl (kv w) ->
    live (now_ms w) (v, dl) = true ->
    run env (get_prog kbytes) w = (ORet (DSome v), w).
Proof.
  intros env kbytes v dl w Hm Hl.
  rewrite (get_general env kbytes v dl w Hm), Hl; reflexivity.
Qed.

Corollary get_general_expired_case :
  forall env kbytes v dl w,
    maps_to (string_of_list_ascii kbytes) v dl (kv w) ->
    live (now_ms w) (v, dl) = false ->
    run env (get_prog kbytes) w = (ORet DNone, w).
Proof.
  intros env kbytes v dl w Hm Hl.
  rewrite (get_general env kbytes v dl w Hm), Hl; reflexivity.
Qed.

(* ===== §3  ACCEPTANCE THEOREM (b): general PUT clears the deadline ========= *)

(** wp form: one wp_put step; the frame clause is [find_add_neq] under the key
    inequality side condition — keyed disjointness, adr-0015 §Decision 3. *)
Theorem put_general_wp :
  forall (env : list dval) (kbytes : list ascii) (vv : val) (w : world),
    wp env (put_prog kbytes vv)
       (fun o w' =>
          o = ORet DUnit
          /\ maps_to (string_of_list_ascii kbytes) (eval_val env vv) None (kv w')
          /\ (forall k', k' <> string_of_list_ascii kbytes ->
                M.find k' (kv w') = M.find k' (kv w))
          /\ ctx w' = ctx w /\ now_ms w' = now_ms w /\ trace w' = trace w
          /\ cache w' = cache w /\ journal w' = journal w) w.
Proof.
  intros env kbytes vv w; unfold put_prog.
  wp_step.
  cbn [set_kv kv ctx now_ms trace cache journal].
  repeat split; try reflexivity.
  - apply maps_to_add_eq.
  - intros k' Hk; apply find_add_neq; exact Hk.
Qed.

(** Run form. *)
Theorem put_general :
  forall env kbytes vv w,
    exists w',
      run env (put_prog kbytes vv) w = (ORet DUnit, w')
      /\ maps_to (string_of_list_ascii kbytes) (eval_val env vv) None (kv w')
      /\ (forall k', k' <> string_of_list_ascii kbytes ->
            M.find k' (kv w') = M.find k' (kv w))
      /\ ctx w' = ctx w /\ now_ms w' = now_ms w /\ trace w' = trace w
      /\ cache w' = cache w /\ journal w' = journal w.
Proof.
  intros env kbytes vv w.
  pose proof (put_general_wp env kbytes vv w) as W; unfold wp in W.
  revert W; destruct (run env (put_prog kbytes vv) w) as [o w']; intro W.
  destruct W as [-> W]; exists w'; split; [reflexivity | exact W].
Qed.

(* ===== §4  Inhabitance (explicit witnesses from the existing corpus) ======= *)

(** The demo world: TimeStore.v's concrete deadline-carrying store
    ([deadline_state_inhabited] / the [sample_ttl] corpus shape — key "a" bound to
    (DInt 7, deadline 1000)), placed AT the boundary instant now = dl = 1000 and
    just past it (now = 1001). *)
Definition demo_state : state :=
  M.add "a"%string (DInt 7, Some 1000) (M.empty entry).
Definition demo_world : world :=
  mkWorld demo_state DUnit 1000 [] (M.empty dval) [] (M.empty (list ascii)) [] 3 [] [] [] 1.
Definition demo_world_expired : world :=
  mkWorld demo_state DUnit 1001 [] (M.empty dval) [] (M.empty (list ascii)) [] 3 [] [] [] 1.
Definition akey : list ascii := list_ascii_of_string "a".

(** [get_general]'s hypotheses are satisfiable on BOTH sides of the boundary —
    explicit witnesses, vm_compute on closed conjuncts only. *)
Lemma get_general_pre_inhabited_live :
  exists w kbytes v dl,
    maps_to (string_of_list_ascii kbytes) v dl (kv w)
    /\ live (now_ms w) (v, dl) = true.
Proof.
  exists demo_world, akey, (DInt 7), (Some 1000).
  split; vm_compute; reflexivity.
Qed.

Lemma get_general_pre_inhabited_expired :
  exists w kbytes v dl,
    maps_to (string_of_list_ascii kbytes) v dl (kv w)
    /\ live (now_ms w) (v, dl) = false.
Proof.
  exists demo_world_expired, akey, (DInt 7), (Some 1000).
  split; vm_compute; reflexivity.
Qed.

(** [put_general]'s postcondition is realizable: an actual post-world exists whose
    binding is deadline-CLEARED (the pre-world's deadline was Some 1000). *)
Lemma put_general_post_inhabited :
  exists w', maps_to (string_of_list_ascii akey) (DInt 42) None (kv w').
Proof.
  exists (snd (run [] (put_prog akey (VInt 42)) demo_world)).
  vm_compute; reflexivity.
Qed.

(* ===== §5  The general theorems against the vm_compute corpus ============== *)

(** Concrete corollary of (a) at the exact boundary, by vm_compute... *)
Example get_at_boundary_concrete :
  run [] (get_prog akey) demo_world = (ORet (DSome (DInt 7)), demo_world).
Proof. vm_compute. reflexivity. Qed.

(** ... and the SAME fact derived from the general theorem (subsumption). *)
Example get_at_boundary_via_general :
  run [] (get_prog akey) demo_world = (ORet (DSome (DInt 7)), demo_world).
Proof.
  rewrite (get_general [] akey (DInt 7) (Some 1000) demo_world);
    [reflexivity | vm_compute; reflexivity].
Qed.

(** Past the boundary the same store answers DNone (dead strictly after). *)
Example get_past_boundary_concrete :
  run [] (get_prog akey) demo_world_expired = (ORet DNone, demo_world_expired).
Proof. vm_compute. reflexivity. Qed.

(** Concrete corollary of (b): value stored, deadline Some 1000 -> None. *)
Example put_clears_deadline_concrete :
  M.find "a"%string (kv (snd (run [] (put_prog akey (VInt 42)) demo_world)))
  = Some (DInt 42, None).
Proof. vm_compute. reflexivity. Qed.

(* ===== §6  MUTANT falsification (the spec has teeth) ======================= *)

(** Under TimeStore.v's [run_mut] — the <-liveness mutant, dead AT the deadline —
    the general GET spec is FALSE: at [demo_world] (now = dl = 1000) the spec demands
    ORet (DSome (DInt 7)) (live AT the deadline), but the mutant answers ORet DNone.
    The counterexample is exhibited concretely (adr-0015 §Decision 5: concrete
    suffices); it sits exactly at the oracle-validated boundary. *)
Theorem get_general_falsified_under_mutant :
  ~ (forall env kbytes v dl w,
       maps_to (string_of_list_ascii kbytes) v dl (kv w) ->
       run_mut env (get_prog kbytes) w
       = (ORet (if live (now_ms w) (v, dl) then DSome v else DNone), w)).
Proof.
  intro H.
  assert (Hm : maps_to (string_of_list_ascii akey) (DInt 7) (Some 1000)
                       (kv demo_world))
    by (vm_compute; reflexivity).
  specialize (H [] akey (DInt 7) (Some 1000) demo_world Hm).
  apply (f_equal fst) in H; vm_compute in H; discriminate H.
Qed.

(** The mutant's concrete face at the boundary, and the observable disagreement with
    the reference on the very program the general theorem covers. *)
Example mutant_get_dead_at_boundary :
  fst (run_mut [] (get_prog akey) demo_world) = ORet DNone.
Proof. vm_compute. reflexivity. Qed.

Example mutant_observably_differs_on_get :
  fst (run [] (get_prog akey) demo_world)
  <> fst (run_mut [] (get_prog akey) demo_world).
Proof. vm_compute. intro H. discriminate H. Qed.

(* ===== §7  Toolkit exercise: triple sugar, Match, Repeat, Fold ============= *)

(** The Hoare-triple sugar in action (adr-0015 §Decision 1): the general GET as a
    triple, the run instant carried by a logical parameter. *)
Theorem get_general_triple :
  forall env kbytes v dl now,
    env |- {{ fun w => maps_to (string_of_list_ascii kbytes) v dl (kv w)
                       /\ now_ms w = now }}
           (get_prog kbytes)
           {{ fun o _ => o = ORet (if live now (v, dl) then DSome v else DNone) }}.
Proof.
  intros env kbytes v dl now w [Hm Hnow]; subst now.
  eapply wp_conseq; [apply (get_general_wp env kbytes v dl w Hm) |].
  intros o w' [Ho _]; exact Ho.
Qed.

(** MATCH rules in action — the read-then-dispatch shape of [incr_at]: return the
    wrapped value on a live hit, DInt 0 on a miss. wp_auto walks the whole
    skip/here/ret chain once the scrutinee's shape is known. *)
Definition get_or_zero (kbytes : list ascii) : tm :=
  Bind (Perform OGet [VBytes kbytes])
       (Match (VVar 0)
          [(PNone, Ret (VInt 0)); (PSome, Ret (VVar 0))]
          (Ret (VInt (-1)))).

Theorem get_or_zero_general_live :
  forall env kbytes v dl w,
    live_at (now_ms w) (string_of_list_ascii kbytes) v dl (kv w) ->
    run env (get_or_zero kbytes) w = (ORet v, w).
Proof.
  intros env kbytes v dl w Hl.
  assert (W : wp env (get_or_zero kbytes)
                 (fun o w' => o = ORet v /\ w' = w) w).
  { unfold get_or_zero; wp_step.
    eapply wp_get_live; [reflexivity | exact Hl |]; wp_simpl.
    wp_auto. }
  unfold wp in W; revert W.
  destruct (run env (get_or_zero kbytes) w) as [o w']; intros [-> ->]; reflexivity.
Qed.

Theorem get_or_zero_general_gone :
  forall env kbytes w,
    gone_at (now_ms w) (string_of_list_ascii kbytes) (kv w) ->
    run env (get_or_zero kbytes) w = (ORet (DInt 0), w).
Proof.
  intros env kbytes w Hg.
  assert (W : wp env (get_or_zero kbytes)
                 (fun o w' => o = ORet (DInt 0) /\ w' = w) w).
  { unfold get_or_zero; wp_step.
    eapply wp_get_gone; [reflexivity | exact Hg |]; wp_simpl.
    wp_auto. }
  unfold wp in W; revert W.
  destruct (run env (get_or_zero kbytes) w) as [o w']; intros [-> ->]; reflexivity.
Qed.

(** REPEAT invariant rule in action: n traces of the same value — the final trace is
    exactly n copies prepended (newest-first), ∀ n. The invariant pins the world
    exactly (the [set_trace_id] eta lemma discharges I 0). *)
Theorem repeat_trace_general :
  forall env (n : nat) (z : Z) w,
    run env (Repeat n (Perform OTrace [VInt z])) w
    = (ORet DUnit, set_trace w (List.repeat (DInt z) n ++ trace w)).
Proof.
  intros env n z w.
  assert (W : wp env (Repeat n (Perform OTrace [VInt z]))
                 (fun o w' => o = ORet DUnit
                              /\ w' = set_trace w (List.repeat (DInt z) n ++ trace w))
                 w).
  { apply (wp_repeat_inv env n _
             (fun i w0 => w0 = set_trace w (List.repeat (DInt z) i ++ trace w))).
    - symmetry; apply set_trace_id.
    - intros i w0 _ HI; apply wp_trace; wp_simpl; rewrite HI; reflexivity.
    - intros w1 HI; split; [reflexivity | exact HI]. }
  unfold wp in W; revert W.
  destruct (run env (Repeat n (Perform OTrace [VInt z])) w) as [o w'];
    intros [-> ->]; reflexivity.
Qed.

(** FOLD invariant rule in action — the R13 collecting-fold shape (acc = the DList
    under construction, body snocs): rebuilding a list element by element is the
    identity, ∀ lists — a data-dependent-length general theorem. The invariant is
    over the processed prefix × accumulator, exactly adr-0015 §Decision 2. *)
Definition rebuild_prog (scrut : val) : tm :=
  Fold scrut (Ret (VList [])) (Prim PListSnoc [VVar 0; VVar 1]).

Theorem fold_rebuild_general :
  forall env scrut vs w,
    eval_val env scrut = DList vs ->
    run env (rebuild_prog scrut) w = (ORet (DList vs), w).
Proof.
  intros env scrut vs w Hs.
  assert (W : wp env (rebuild_prog scrut)
                 (fun o w' => o = ORet (DList vs) /\ w' = w) w).
  { unfold rebuild_prog.
    apply (wp_fold_inv env scrut _ _ vs
             (fun pre acc w0 => acc = DList pre /\ w0 = w)); [exact Hs | | |].
    - apply wp_ret; wp_simpl; split; reflexivity.
    - intros pre x post acc w0 Hsplit [Hacc Hw]; subst acc w0.
      eapply wp_prim_list_snoc; [reflexivity |].
      wp_simpl; split; reflexivity.
    - intros acc w1 [Hacc Hw]; subst acc w1; split; reflexivity. }
  unfold wp in W; revert W.
  destruct (run env (rebuild_prog scrut) w) as [o w']; intros [-> ->]; reflexivity.
Qed.

(** Print Assumptions footprint — each must say "Closed under the global context". *)
Print Assumptions get_general_wp.
Print Assumptions get_general.
Print Assumptions get_general_live_case.
Print Assumptions get_general_expired_case.
Print Assumptions put_general_wp.
Print Assumptions put_general.
Print Assumptions get_general_pre_inhabited_live.
Print Assumptions get_general_pre_inhabited_expired.
Print Assumptions put_general_post_inhabited.
Print Assumptions get_at_boundary_concrete.
Print Assumptions get_at_boundary_via_general.
Print Assumptions get_past_boundary_concrete.
Print Assumptions put_clears_deadline_concrete.
Print Assumptions get_general_falsified_under_mutant.
Print Assumptions mutant_get_dead_at_boundary.
Print Assumptions mutant_observably_differs_on_get.
Print Assumptions get_general_triple.
Print Assumptions get_or_zero_general_live.
Print Assumptions get_or_zero_general_gone.
Print Assumptions repeat_trace_general.
Print Assumptions fold_rebuild_general.
