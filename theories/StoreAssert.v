(** * StoreAssert — the keyed store-assertion library for the EffIR program logic
    (R14, adr-0015-program-logic §Decision 3).

    Bespoke and minimal — NOT separation logic: find-based binding assertions over the
    expiring bytes-keyed store, absence/expiry predicates, add/remove/find update
    lemmas under decidable string-key (in)equality side conditions, and the LIVENESS
    lemmas at the boundary (now <=? d, BOTH sides — the adr-0011 oracle-validated
    rule: alive AT the deadline, dead strictly after).

    FMapAVL internals stay Opaque in spirit: every lemma below goes through the
    find/add/remove/empty INTERFACE only, via the stdlib [FMapFacts] functor (whose
    lemmas are proven once in the stdlib against the FMap interface — using them never
    unfolds the AVL representation, so the Opaque discipline of theories/Prims.v is
    respected).

    Layers:
    §1  find/add/remove/empty interface lemmas (elt-polymorphic).
    §2  Binding assertions: [maps_to] (physical, M.find-based), [absent],
        [live_at] / [gone_at] (the live view every store op actually sees).
    §3  Liveness at the boundary (now <=? d, both sides).
    §4  Bridges between the physical and the live view.
    §5  maps_to / absent / live_at / gone_at under M.add and M.remove. *)

From Stdlib Require Import ZArith List FMapFacts OrderedTypeEx String Ascii Bool Lia.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

(** Interface facts for the string-keyed map [M] (EffIR). [String_as_OT.eq] is
    definitionally Logic.eq, so the side conditions below are plain [<>]. *)
Module MF := FMapFacts.WFacts_fun String_as_OT M.

(* ===== §1  find/add/remove/empty interface lemmas ========================== *)

Lemma find_add_eq : forall (A : Type) (k : string) (e : A) (s : M.t A),
  M.find k (M.add k e s) = Some e.
Proof. intros; apply MF.add_eq_o; reflexivity. Qed.

Lemma find_add_neq : forall (A : Type) (k k' : string) (e : A) (s : M.t A),
  k' <> k -> M.find k' (M.add k e s) = M.find k' s.
Proof. intros; apply MF.add_neq_o; congruence. Qed.

Lemma find_remove_eq : forall (A : Type) (k : string) (s : M.t A),
  M.find k (M.remove k s) = None.
Proof. intros; apply MF.remove_eq_o; reflexivity. Qed.

Lemma find_remove_neq : forall (A : Type) (k k' : string) (s : M.t A),
  k' <> k -> M.find k' (M.remove k s) = M.find k' s.
Proof. intros; apply MF.remove_neq_o; congruence. Qed.

Lemma find_empty : forall (A : Type) (k : string), M.find k (M.empty A) = None.
Proof. intros; apply MF.empty_o. Qed.

(** String keys have decidable equality — every (in)equality side condition above is
    dischargeable. *)
Lemma key_eq_dec : forall k k' : string, {k = k'} + {k <> k'}.
Proof. exact string_dec. Qed.

(* ===== §2  Binding assertions ============================================== *)

(** [maps_to k v dl s]: the store PHYSICALLY binds k to (v, dl) — an M.find fact,
    liveness-agnostic (an expired binding still [maps_to] until physically removed;
    lazy-deletion freedom, adr-0011). *)
Definition maps_to (k : string) (v : dval) (dl : option Z) (s : state) : Prop :=
  M.find k s = Some (v, dl).

(** [absent k s]: no physical binding at all. *)
Definition absent (k : string) (s : state) : Prop := M.find k s = None.

(** [live_at t k v dl s]: k is bound to (v, dl) AND live at instant t — the view every
    store op actually sees ([find_live]-based). *)
Definition live_at (t : Z) (k : string) (v : dval) (dl : option Z) (s : state) : Prop :=
  find_live t k s = Some (v, dl).

(** [gone_at t k s]: absent-or-expired at instant t — semantically absent for every op
    and for [observe] (adr-0011 §Decision 3). *)
Definition gone_at (t : Z) (k : string) (s : state) : Prop :=
  find_live t k s = None.

(* ===== §3  Liveness at the boundary (now <=? d, both sides) ================ *)

Lemma live_no_deadline : forall t v, live t (v, None) = true.
Proof. reflexivity. Qed.

Lemma live_iff : forall t (v : dval) d, live t (v, Some d) = true <-> t <= d.
Proof. intros; cbn; apply Z.leb_le. Qed.

Lemma live_before_deadline : forall t (v : dval) d, t <= d -> live t (v, Some d) = true.
Proof. intros t v d H; cbn; apply Z.leb_le; exact H. Qed.

(** Alive AT the exact deadline (the oracle-validated boundary, adr-0011). *)
Lemma live_at_deadline : forall (v : dval) d, live d (v, Some d) = true.
Proof. intros; cbn; apply Z.leb_refl. Qed.

(** Dead strictly past it. *)
Lemma dead_past_deadline : forall t (v : dval) d, d < t -> live t (v, Some d) = false.
Proof. intros t v d H; cbn; apply Z.leb_gt; exact H. Qed.

Lemma dead_iff : forall t (v : dval) d, live t (v, Some d) = false <-> d < t.
Proof. intros; cbn; apply Z.leb_gt. Qed.

(* ===== §4  Bridges between the physical and the live view ================== *)

(** The ONE unfolding a store-op rule needs: a physical binding's live view is decided
    by [live] at the instant. *)
Lemma find_live_maps_to : forall t k v dl s,
  maps_to k v dl s ->
  find_live t k s = if live t (v, dl) then Some (v, dl) else None.
Proof. intros t k v dl s H; unfold find_live; rewrite H; reflexivity. Qed.

Lemma live_at_intro : forall t k v dl s,
  maps_to k v dl s -> live t (v, dl) = true -> live_at t k v dl s.
Proof.
  intros t k v dl s Hm Hl; unfold live_at.
  rewrite (find_live_maps_to t k v dl s Hm), Hl; reflexivity.
Qed.

Lemma live_at_elim : forall t k v dl s,
  live_at t k v dl s -> maps_to k v dl s /\ live t (v, dl) = true.
Proof.
  intros t k v dl s H; unfold live_at, find_live in H.
  destruct (M.find k s) as [e |] eqn:E; [| discriminate].
  destruct (live t e) eqn:L; [| discriminate].
  inversion H; subst; split; [exact E | exact L].
Qed.

Lemma gone_at_absent : forall t k s, absent k s -> gone_at t k s.
Proof. intros t k s H; unfold gone_at, find_live; rewrite H; reflexivity. Qed.

Lemma gone_at_expired : forall t k v d s,
  maps_to k v (Some d) s -> d < t -> gone_at t k s.
Proof.
  intros t k v d s Hm Hd; unfold gone_at.
  rewrite (find_live_maps_to t k v (Some d) s Hm).
  rewrite (dead_past_deadline t v d Hd); reflexivity.
Qed.

Lemma gone_at_elim : forall t k s,
  gone_at t k s -> absent k s \/ exists v d, maps_to k v (Some d) s /\ d < t.
Proof.
  intros t k s H; unfold gone_at, find_live in H.
  destruct (M.find k s) as [[v [d |]] |] eqn:E.
  - (* Some (v, Some d): the liveness test decided *)
    destruct (live t (v, Some d)) eqn:L; [discriminate |].
    right; exists v, d; split; [exact E | apply (proj1 (dead_iff t v d)); exact L].
  - (* Some (v, None): always live — contradicts H *)
    cbn in H; discriminate.
  - left; exact E.
Qed.

(* ===== §5  Assertions under M.add / M.remove =============================== *)

Lemma maps_to_add_eq : forall k v dl s, maps_to k v dl (M.add k (v, dl) s).
Proof. intros; unfold maps_to; apply find_add_eq. Qed.

Lemma maps_to_add_neq : forall k k' v dl (e : entry) s,
  k' <> k -> (maps_to k' v dl (M.add k e s) <-> maps_to k' v dl s).
Proof.
  intros k k' v dl e s H; unfold maps_to.
  rewrite (find_add_neq entry k k' e s H); apply iff_refl.
Qed.

Lemma absent_add_neq : forall k k' (e : entry) s,
  k' <> k -> (absent k' (M.add k e s) <-> absent k' s).
Proof.
  intros k k' e s H; unfold absent.
  rewrite (find_add_neq entry k k' e s H); apply iff_refl.
Qed.

Lemma absent_remove_eq : forall k s, absent k (M.remove k s).
Proof. intros; unfold absent; apply find_remove_eq. Qed.

Lemma maps_to_remove_neq : forall k k' v dl s,
  k' <> k -> (maps_to k' v dl (M.remove k s) <-> maps_to k' v dl s).
Proof.
  intros k k' v dl s H; unfold maps_to.
  rewrite (find_remove_neq entry k k' s H); apply iff_refl.
Qed.

Lemma absent_empty : forall k, absent k (M.empty entry).
Proof. intros; unfold absent; apply find_empty. Qed.

(** The live view under updates: adding a binding makes it live_at any instant that
    [live]-accepts its deadline; every OTHER key's live view is untouched (the keyed
    frame shape, adr-0015 §Decision 3 — keyed disjointness, not separation logic). *)
Lemma live_at_add_eq : forall t k v dl s,
  live t (v, dl) = true -> live_at t k v dl (M.add k (v, dl) s).
Proof. intros t k v dl s H; apply live_at_intro; [apply maps_to_add_eq | exact H]. Qed.

Lemma gone_at_add_eq : forall t k v dl s,
  live t (v, dl) = false -> gone_at t k (M.add k (v, dl) s).
Proof.
  intros t k v dl s H; unfold gone_at.
  rewrite (find_live_maps_to t k v dl _ (maps_to_add_eq k v dl s)), H; reflexivity.
Qed.

Lemma live_at_add_neq : forall t k k' v dl (e : entry) s,
  k' <> k -> (live_at t k' v dl (M.add k e s) <-> live_at t k' v dl s).
Proof.
  intros t k k' v dl e s H; unfold live_at, find_live.
  rewrite (find_add_neq entry k k' e s H); apply iff_refl.
Qed.

Lemma gone_at_add_neq : forall t k k' (e : entry) s,
  k' <> k -> (gone_at t k' (M.add k e s) <-> gone_at t k' s).
Proof.
  intros t k k' e s H; unfold gone_at, find_live.
  rewrite (find_add_neq entry k k' e s H); apply iff_refl.
Qed.

Lemma gone_at_remove_eq : forall t k s, gone_at t k (M.remove k s).
Proof. intros; apply gone_at_absent, absent_remove_eq. Qed.

Lemma live_at_remove_neq : forall t k k' v dl s,
  k' <> k -> (live_at t k' v dl (M.remove k s) <-> live_at t k' v dl s).
Proof.
  intros t k k' v dl s H; unfold live_at, find_live.
  rewrite (find_remove_neq entry k k' s H); apply iff_refl.
Qed.

Lemma gone_at_remove_neq : forall t k k' s,
  k' <> k -> (gone_at t k' (M.remove k s) <-> gone_at t k' s).
Proof.
  intros t k k' s H; unfold gone_at, find_live.
  rewrite (find_remove_neq entry k k' s H); apply iff_refl.
Qed.

Lemma gone_at_empty : forall t k, gone_at t k (M.empty entry).
Proof. intros; apply gone_at_absent, absent_empty. Qed.

(** Print Assumptions footprint — each must say "Closed under the global context". *)
Print Assumptions find_add_eq.
Print Assumptions find_add_neq.
Print Assumptions find_remove_eq.
Print Assumptions find_remove_neq.
Print Assumptions find_empty.
Print Assumptions find_live_maps_to.
Print Assumptions live_at_deadline.
Print Assumptions dead_past_deadline.
Print Assumptions gone_at_elim.
Print Assumptions maps_to_add_eq.
Print Assumptions live_at_add_eq.
Print Assumptions gone_at_remove_eq.
