(** * Logic — the EffIR program logic (R14, adr-0015-program-logic).

    A SHALLOW weakest-precondition layer over the existing [run] — no second semantics
    (invariant 1 intact): [wp env t Q w] is BY DEFINITION a statement about
    [run env t w], so adequacy is trivial and a wp theorem IS a run theorem by
    unfolding. The value of this file is the RULE LIBRARY (each rule a lemma proven
    against [run], once) and the tactics that apply it (theories/LogicTactics.v).

    Contents (adr-0015 §Decision 1–2):
    §1  [wp], Hoare-triple sugar, adequacy + consequence glue, world plumbing.
    §2  Structural rules: [wp_ret]; [wp_bind] in THE one outcome-split shape used
        everywhere (the continuation postcondition matches on the outcome, so OErr
        short-circuiting falls out of the rule rather than needing a side calculus);
        [wp_bind_err] for a known-aborting prefix.
    §3  Perform rules, one per op (all 12): the store ops are phrased via the
        StoreAssert live view at [world.now_ms] (base rule with the exact
        [handle_store] result + derived live/gone splits); ONow/OAsk/OThrow/OTrace/
        OJournal/OCacheGet/OCachePut each state their exact world transition from
        [run]'s definition.
    §4  Prim rules: generic [wp_prim] + one spec lemma per prim (16, incl. PListSnoc),
        mirroring [apply_prim] — pure steps, world unchanged.
    §5  Match rules (taken branch / skip / default — first-match-wins, syntax-directed)
        + [match_pat] inversion helpers, one per pattern (8).
    §6  Repeat: index-carrying invariant rule [wp_repeat_inv] with the OErr escape.
    §7  Fold: invariant rule [wp_fold_inv] over processed-prefix × accumulator with the
        OErr escape, plus the non-DList empty-fold rule.

    Proof style: the Journal.v twin-equation technique ([repeat_loop] / [fold_elems] /
    [try_branches] + run_*_eq, plus local one-step equations) for [run]'s nested fixes;
    whitelisted [cbn] only; NEVER vm_compute on an open term (theories/Prims.v header —
    observed multi-GB blowups). Loop invariants and Match splits remain user-supplied:
    this is a proof toolkit, not full automation (adr-0015 §Decision 4). *)

From Stdlib Require Import ZArith List String Ascii Bool Lia.
From Rocqeteer Require Import EffIR StoreAssert Journal.
Import ListNotations.
Local Open Scope Z_scope.

(* ===== §1  wp, triples, adequacy =========================================== *)

(** THE definition (adr-0015 §Decision 1): shallow, [run] stays the only truth. *)
Definition wp (env : list dval) (t : tm) (Q : outcome -> world -> Prop)
  : world -> Prop :=
  fun w => let '(o, w') := run env t w in Q o w'.

(** Hoare-triple sugar: [env |- {{ P }} t {{ Q }}] is [forall w, P w -> wp env t Q w]. *)
Definition triple (env : list dval) (P : world -> Prop) (t : tm)
                  (Q : outcome -> world -> Prop) : Prop :=
  forall w, P w -> wp env t Q w.

Notation "env '|-' '{{' P '}}' t '{{' Q '}}'" := (triple env P t Q)
  (at level 100, t at level 39, P at level 99, Q at level 99).

(** Adequacy is definitional: a wp fact IS a run fact (zero new trusted surface). *)
Lemma wp_run : forall env t Q w o w',
  run env t w = (o, w') -> wp env t Q w -> Q o w'.
Proof. intros env t Q w o w' E H; unfold wp in H; rewrite E in H; exact H. Qed.

Lemma run_wp : forall env t Q w o w',
  run env t w = (o, w') -> Q o w' -> wp env t Q w.
Proof. intros env t Q w o w' E H; unfold wp; rewrite E; exact H. Qed.

(** Consequence (postcondition weakening). *)
Lemma wp_conseq : forall env t (Q1 Q2 : outcome -> world -> Prop) w,
  wp env t Q1 w -> (forall o w', Q1 o w' -> Q2 o w') -> wp env t Q2 w.
Proof.
  intros env t Q1 Q2 w H Himp; unfold wp in *.
  destruct (run env t w) as [o w']; apply Himp, H.
Qed.

Lemma triple_conseq :
  forall env (P P' : world -> Prop) t (Q Q' : outcome -> world -> Prop),
    triple env P t Q ->
    (forall w, P' w -> P w) ->
    (forall o w', Q o w' -> Q' o w') ->
    triple env P' t Q'.
Proof.
  intros env P P' t Q Q' H Hpre Hpost w Hw.
  apply (wp_conseq env t Q); [apply H, Hpre, Hw | exact Hpost].
Qed.

(** World plumbing: rebuilding a world from one of its own fields is the identity
    (record eta) — this is why the read-only store ops leave the world LITERALLY
    unchanged, and how loop invariants pin worlds exactly. *)
Lemma set_kv_id : forall w, set_kv w (kv w) = w.
Proof. destruct w; reflexivity. Qed.

Lemma set_trace_id : forall w, set_trace w (trace w) = w.
Proof. destruct w; reflexivity. Qed.

Lemma set_cache_id : forall w, set_cache w (cache w) = w.
Proof. destruct w; reflexivity. Qed.

Lemma set_journal_id : forall w, set_journal w (journal w) = w.
Proof. destruct w; reflexivity. Qed.

(* ===== §2  Structural rules ================================================ *)

Lemma wp_ret : forall env v Q w,
  Q (ORet (eval_val env v)) w -> wp env (Ret v) Q w.
Proof. intros env v Q w H; exact H. Qed.

(** THE Bind rule (outcome-split formulation — the one shape used everywhere): the
    continuation runs with the intermediate dval PUSHED onto the env (de Bruijn 0);
    an OErr outcome of the prefix short-circuits straight into Q. *)
Lemma wp_bind : forall env t1 t2 Q w,
  wp env t1 (fun o w' => match o with
                         | ORet x => wp (x :: env) t2 Q w'
                         | OErr e => Q (OErr e) w'
                         end) w ->
  wp env (Bind t1 t2) Q w.
Proof.
  intros env t1 t2 Q w H; unfold wp in *; cbn [run].
  revert H; destruct (run env t1 w) as [[x | e] w']; intro H; exact H.
Qed.

(** Bind error propagation with a known-aborting prefix. *)
Lemma wp_bind_err : forall env t1 t2 Q w e w',
  run env t1 w = (OErr e, w') -> Q (OErr e) w' -> wp env (Bind t1 t2) Q w.
Proof.
  intros env t1 t2 Q w e w' E H; unfold wp; cbn [run]; rewrite E; exact H.
Qed.

(* ===== §3  Perform rules (one per op) ====================================== *)

(** Named result shapes of the store ops ([handle_store]'s branches, verbatim — each
    is definitionally equal to the corresponding match, so the base rules convert). *)
Definition get_view (e : option entry) : dval :=
  match e with Some (v, _) => DSome v | None => DNone end.

Definition del_view (e : option entry) : dval :=
  match e with Some _ => DBool true | None => DBool false end.

Definition deadline_view (e : option entry) : dval :=
  match e with
  | Some (_, None)   => DSome DNone
  | Some (_, Some d) => DSome (DSome (DInt d))
  | None             => DNone
  end.

(** --- OGet ---------------------------------------------------------------- *)

Lemma wp_get : forall env a ks Q w,
  eval_val env a = DBytes ks ->
  Q (ORet (get_view (find_live (now_ms w) (string_of_list_ascii ks) (kv w)))) w ->
  wp env (Perform OGet [a]) Q w.
Proof.
  intros env a ks Q w Ha HQ; unfold wp; cbn [run map].
  rewrite Ha; cbn [handle_store]; rewrite set_kv_id; exact HQ.
Qed.

Lemma wp_get_live : forall env a ks v dl Q w,
  eval_val env a = DBytes ks ->
  live_at (now_ms w) (string_of_list_ascii ks) v dl (kv w) ->
  Q (ORet (DSome v)) w ->
  wp env (Perform OGet [a]) Q w.
Proof.
  intros env a ks v dl Q w Ha Hl HQ; eapply wp_get; [exact Ha |].
  unfold live_at in Hl; rewrite Hl; exact HQ.
Qed.

Lemma wp_get_gone : forall env a ks Q w,
  eval_val env a = DBytes ks ->
  gone_at (now_ms w) (string_of_list_ascii ks) (kv w) ->
  Q (ORet DNone) w ->
  wp env (Perform OGet [a]) Q w.
Proof.
  intros env a ks Q w Ha Hg HQ; eapply wp_get; [exact Ha |].
  unfold gone_at in Hg; rewrite Hg; exact HQ.
Qed.

(** --- OPut (stores the value and CLEARS any deadline) ---------------------- *)

Lemma wp_put : forall env a b ks Q w,
  eval_val env a = DBytes ks ->
  Q (ORet DUnit)
    (set_kv w (M.add (string_of_list_ascii ks) (eval_val env b, None) (kv w))) ->
  wp env (Perform OPut [a; b]) Q w.
Proof.
  intros env a b ks Q w Ha HQ; unfold wp; cbn [run map].
  rewrite Ha; cbn [handle_store]; exact HQ.
Qed.

(** --- ODelete (true iff a LIVE binding was removed) ------------------------ *)

Lemma wp_delete : forall env a ks Q w,
  eval_val env a = DBytes ks ->
  Q (ORet (del_view (find_live (now_ms w) (string_of_list_ascii ks) (kv w))))
    (set_kv w (M.remove (string_of_list_ascii ks) (kv w))) ->
  wp env (Perform ODelete [a]) Q w.
Proof.
  intros env a ks Q w Ha HQ; unfold wp; cbn [run map].
  rewrite Ha; cbn [handle_store]; exact HQ.
Qed.

Lemma wp_delete_live : forall env a ks v dl Q w,
  eval_val env a = DBytes ks ->
  live_at (now_ms w) (string_of_list_ascii ks) v dl (kv w) ->
  Q (ORet (DBool true)) (set_kv w (M.remove (string_of_list_ascii ks) (kv w))) ->
  wp env (Perform ODelete [a]) Q w.
Proof.
  intros env a ks v dl Q w Ha Hl HQ; eapply wp_delete; [exact Ha |].
  unfold live_at in Hl; rewrite Hl; exact HQ.
Qed.

Lemma wp_delete_gone : forall env a ks Q w,
  eval_val env a = DBytes ks ->
  gone_at (now_ms w) (string_of_list_ascii ks) (kv w) ->
  Q (ORet (DBool false)) (set_kv w (M.remove (string_of_list_ascii ks) (kv w))) ->
  wp env (Perform ODelete [a]) Q w.
Proof.
  intros env a ks Q w Ha Hg HQ; eapply wp_delete; [exact Ha |].
  unfold gone_at in Hg; rewrite Hg; exact HQ.
Qed.

(** --- OGetDeadline (nested-option encoding) -------------------------------- *)

Lemma wp_get_deadline : forall env a ks Q w,
  eval_val env a = DBytes ks ->
  Q (ORet (deadline_view (find_live (now_ms w) (string_of_list_ascii ks) (kv w)))) w ->
  wp env (Perform OGetDeadline [a]) Q w.
Proof.
  intros env a ks Q w Ha HQ; unfold wp; cbn [run map].
  rewrite Ha; cbn [handle_store]; rewrite set_kv_id; exact HQ.
Qed.

Lemma wp_get_deadline_live : forall env a ks v dl Q w,
  eval_val env a = DBytes ks ->
  live_at (now_ms w) (string_of_list_ascii ks) v dl (kv w) ->
  Q (ORet (deadline_view (Some (v, dl)))) w ->
  wp env (Perform OGetDeadline [a]) Q w.
Proof.
  intros env a ks v dl Q w Ha Hl HQ; eapply wp_get_deadline; [exact Ha |].
  unfold live_at in Hl; rewrite Hl; exact HQ.
Qed.

Lemma wp_get_deadline_gone : forall env a ks Q w,
  eval_val env a = DBytes ks ->
  gone_at (now_ms w) (string_of_list_ascii ks) (kv w) ->
  Q (ORet DNone) w ->
  wp env (Perform OGetDeadline [a]) Q w.
Proof.
  intros env a ks Q w Ha Hg HQ; eapply wp_get_deadline; [exact Ha |].
  unfold gone_at in Hg; rewrite Hg; exact HQ.
Qed.

(** --- OSetDeadline (both payload shapes; true iff a live binding modified) -- *)

Lemma wp_set_deadline_some : forall env a b ks d Q w,
  eval_val env a = DBytes ks ->
  eval_val env b = DSome (DInt d) ->
  match find_live (now_ms w) (string_of_list_ascii ks) (kv w) with
  | Some (v, _) =>
      Q (ORet (DBool true))
        (set_kv w (M.add (string_of_list_ascii ks) (v, Some d) (kv w)))
  | None => Q (ORet (DBool false)) w
  end ->
  wp env (Perform OSetDeadline [a; b]) Q w.
Proof.
  intros env a b ks d Q w Ha Hb HQ; unfold wp; cbn [run map].
  rewrite Ha, Hb; cbn [handle_store]; revert HQ.
  destruct (find_live (now_ms w) (string_of_list_ascii ks) (kv w)) as [[v dl] |];
    intro HQ; [exact HQ | rewrite set_kv_id; exact HQ].
Qed.

Lemma wp_set_deadline_none : forall env a b ks Q w,
  eval_val env a = DBytes ks ->
  eval_val env b = DNone ->
  match find_live (now_ms w) (string_of_list_ascii ks) (kv w) with
  | Some (v, _) =>
      Q (ORet (DBool true))
        (set_kv w (M.add (string_of_list_ascii ks) (v, None) (kv w)))
  | None => Q (ORet (DBool false)) w
  end ->
  wp env (Perform OSetDeadline [a; b]) Q w.
Proof.
  intros env a b ks Q w Ha Hb HQ; unfold wp; cbn [run map].
  rewrite Ha, Hb; cbn [handle_store]; revert HQ.
  destruct (find_live (now_ms w) (string_of_list_ascii ks) (kv w)) as [[v dl] |];
    intro HQ; [exact HQ | rewrite set_kv_id; exact HQ].
Qed.

Lemma wp_set_deadline_some_live : forall env a b ks d v dl Q w,
  eval_val env a = DBytes ks ->
  eval_val env b = DSome (DInt d) ->
  live_at (now_ms w) (string_of_list_ascii ks) v dl (kv w) ->
  Q (ORet (DBool true))
    (set_kv w (M.add (string_of_list_ascii ks) (v, Some d) (kv w))) ->
  wp env (Perform OSetDeadline [a; b]) Q w.
Proof.
  intros env a b ks d v dl Q w Ha Hb Hl HQ.
  eapply wp_set_deadline_some; [exact Ha | exact Hb |].
  unfold live_at in Hl; rewrite Hl; exact HQ.
Qed.

Lemma wp_set_deadline_some_gone : forall env a b ks d Q w,
  eval_val env a = DBytes ks ->
  eval_val env b = DSome (DInt d) ->
  gone_at (now_ms w) (string_of_list_ascii ks) (kv w) ->
  Q (ORet (DBool false)) w ->
  wp env (Perform OSetDeadline [a; b]) Q w.
Proof.
  intros env a b ks d Q w Ha Hb Hg HQ.
  eapply wp_set_deadline_some; [exact Ha | exact Hb |].
  unfold gone_at in Hg; rewrite Hg; exact HQ.
Qed.

Lemma wp_set_deadline_none_live : forall env a b ks v dl Q w,
  eval_val env a = DBytes ks ->
  eval_val env b = DNone ->
  live_at (now_ms w) (string_of_list_ascii ks) v dl (kv w) ->
  Q (ORet (DBool true))
    (set_kv w (M.add (string_of_list_ascii ks) (v, None) (kv w))) ->
  wp env (Perform OSetDeadline [a; b]) Q w.
Proof.
  intros env a b ks v dl Q w Ha Hb Hl HQ.
  eapply wp_set_deadline_none; [exact Ha | exact Hb |].
  unfold live_at in Hl; rewrite Hl; exact HQ.
Qed.

Lemma wp_set_deadline_none_gone : forall env a b ks Q w,
  eval_val env a = DBytes ks ->
  eval_val env b = DNone ->
  gone_at (now_ms w) (string_of_list_ascii ks) (kv w) ->
  Q (ORet (DBool false)) w ->
  wp env (Perform OSetDeadline [a; b]) Q w.
Proof.
  intros env a b ks Q w Ha Hb Hg HQ.
  eapply wp_set_deadline_none; [exact Ha | exact Hb |].
  unfold gone_at in Hg; rewrite Hg; exact HQ.
Qed.

(** --- ONow / OAsk / OThrow (world untouched; OThrow aborts) ---------------- *)

Lemma wp_now : forall env args Q w,
  Q (ORet (DInt (now_ms w))) w -> wp env (Perform ONow args) Q w.
Proof. intros env args Q w H; exact H. Qed.

Lemma wp_ask : forall env args Q w,
  Q (ORet (ctx w)) w -> wp env (Perform OAsk args) Q w.
Proof. intros env args Q w H; exact H. Qed.

Lemma wp_throw : forall env a args Q w,
  Q (OErr (eval_val env a)) w -> wp env (Perform OThrow (a :: args)) Q w.
Proof. intros env a args Q w H; unfold wp; cbn [run map nth]; exact H. Qed.

(** --- OTrace / OJournal (append newest-first; result DUnit) ---------------- *)

Lemma wp_trace : forall env a Q w,
  Q (ORet DUnit) (set_trace w (eval_val env a :: trace w)) ->
  wp env (Perform OTrace [a]) Q w.
Proof. intros env a Q w H; exact H. Qed.

Lemma wp_journal : forall env a Q w,
  Q (ORet DUnit) (set_journal w ((now_ms w, eval_val env a) :: journal w)) ->
  wp env (Perform OJournal [a]) Q w.
Proof. intros env a Q w H; exact H. Qed.

(** --- OCacheGet / OCachePut (memo store; NOT the expiring store) ----------- *)

Lemma wp_cache_get : forall env a ks Q w,
  eval_val env a = DBytes ks ->
  Q (ORet (opt_to_dval (M.find (string_of_list_ascii ks) (cache w)))) w ->
  wp env (Perform OCacheGet [a]) Q w.
Proof.
  intros env a ks Q w Ha HQ; unfold wp; cbn [run map]; rewrite Ha; exact HQ.
Qed.

Lemma wp_cache_put : forall env a b ks Q w,
  eval_val env a = DBytes ks ->
  Q (ORet DUnit)
    (set_cache w (M.add (string_of_list_ascii ks) (eval_val env b) (cache w))) ->
  wp env (Perform OCachePut [a; b]) Q w.
Proof.
  intros env a b ks Q w Ha HQ; unfold wp; cbn [run map]; rewrite Ha; exact HQ.
Qed.

(* ===== §4  Prim rules (adr-0009 registry, 16 prims) ======================== *)

(** Generic rule: a Prim step is pure — the world is unchanged and the result is
    [apply_prim] on the evaluated arguments. *)
Lemma wp_prim : forall env p args Q w,
  Q (ORet (apply_prim p (map (eval_val env) args))) w ->
  wp env (Prim p args) Q w.
Proof. intros env p args Q w H; exact H. Qed.

(** One spec lemma per prim, mirroring [apply_prim]'s reference definition. *)

Lemma wp_prim_add_checked : forall env a b za zb Q w,
  eval_val env a = DInt za -> eval_val env b = DInt zb ->
  Q (ORet (apply_add_checked za zb)) w ->
  wp env (Prim PAddChecked [a; b]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H, H0; exact H1. Qed.

Lemma wp_prim_sub_checked : forall env a b za zb Q w,
  eval_val env a = DInt za -> eval_val env b = DInt zb ->
  Q (ORet (apply_sub_checked za zb)) w ->
  wp env (Prim PSubChecked [a; b]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H, H0; exact H1. Qed.

Lemma wp_prim_cmp_int : forall env a b za zb Q w,
  eval_val env a = DInt za -> eval_val env b = DInt zb ->
  Q (ORet (apply_cmp_int za zb)) w ->
  wp env (Prim PCmpInt [a; b]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H, H0; exact H1. Qed.

Lemma wp_prim_eq_bytes : forall env a b xs ys Q w,
  eval_val env a = DBytes xs -> eval_val env b = DBytes ys ->
  Q (ORet (DBool (ascii_list_eqb xs ys))) w ->
  wp env (Prim PEqBytes [a; b]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H, H0; exact H1. Qed.

Lemma wp_prim_bytes_len : forall env a xs Q w,
  eval_val env a = DBytes xs ->
  Q (ORet (DInt (Z.of_nat (List.length xs)))) w ->
  wp env (Prim PBytesLen [a]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H; exact H0. Qed.

Lemma wp_prim_bytes_concat : forall env a b xs ys Q w,
  eval_val env a = DBytes xs -> eval_val env b = DBytes ys ->
  Q (ORet (DBytes (xs ++ ys))) w ->
  wp env (Prim PBytesConcat [a; b]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H, H0; exact H1. Qed.

Lemma wp_prim_bytes_sub : forall env a b c xs off len Q w,
  eval_val env a = DBytes xs ->
  eval_val env b = DInt off -> eval_val env c = DInt len ->
  Q (ORet (apply_bytes_sub xs off len)) w ->
  wp env (Prim PBytesSub [a; b; c]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H, H0, H1; exact H2. Qed.

Lemma wp_prim_parse_int64 : forall env a xs Q w,
  eval_val env a = DBytes xs ->
  Q (ORet (apply_parse_int64 xs)) w ->
  wp env (Prim PParseInt64 [a]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H; exact H0. Qed.

Lemma wp_prim_print_int : forall env a z Q w,
  eval_val env a = DInt z ->
  Q (ORet (apply_print_int z)) w ->
  wp env (Prim PPrintInt [a]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H; exact H0. Qed.

Lemma wp_prim_mul_checked : forall env a b za zb Q w,
  eval_val env a = DInt za -> eval_val env b = DInt zb ->
  Q (ORet (apply_mul_checked za zb)) w ->
  wp env (Prim PMulChecked [a; b]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H, H0; exact H1. Qed.

Lemma wp_prim_list_len : forall env a vs Q w,
  eval_val env a = DList vs ->
  Q (ORet (DInt (Z.of_nat (List.length vs)))) w ->
  wp env (Prim PListLen [a]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H; exact H0. Qed.

Lemma wp_prim_list_nth : forall env a b vs i Q w,
  eval_val env a = DList vs -> eval_val env b = DInt i ->
  Q (ORet (apply_list_nth vs i)) w ->
  wp env (Prim PListNth [a; b]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H, H0; exact H1. Qed.

Lemma wp_prim_div_floor : forall env a b za zb Q w,
  eval_val env a = DInt za -> eval_val env b = DInt zb ->
  Q (ORet (apply_div_floor za zb)) w ->
  wp env (Prim PDivFloor [a; b]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H, H0; exact H1. Qed.

Lemma wp_prim_lower_bytes : forall env a xs Q w,
  eval_val env a = DBytes xs ->
  Q (ORet (apply_lower_bytes xs)) w ->
  wp env (Prim PLowerBytes [a]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H; exact H0. Qed.

Lemma wp_prim_upper_bytes : forall env a xs Q w,
  eval_val env a = DBytes xs ->
  Q (ORet (apply_upper_bytes xs)) w ->
  wp env (Prim PUpperBytes [a]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H; exact H0. Qed.

Lemma wp_prim_list_snoc : forall env a b vs Q w,
  eval_val env a = DList vs ->
  Q (ORet (DList (vs ++ [eval_val env b]))) w ->
  wp env (Prim PListSnoc [a; b]) Q w.
Proof. intros; apply wp_prim; cbn [map]; rewrite H; exact H0. Qed.

(* ===== §5  Match rules ===================================================== *)

(** One-step twin equations for [try_branches] (Journal.v twin of [run]'s nested fix),
    so the rules rewrite instead of cbn-ing into an anonymous fix. *)
Lemma try_branches_nil_eq : forall env d default w,
  try_branches env d default w [] = run env default w.
Proof. reflexivity. Qed.

Lemma try_branches_cons_eq : forall env d default w p body rest,
  try_branches env d default w ((p, body) :: rest)
  = match match_pat p d with
    | Some payloads => run (push_env payloads env) body w
    | None          => try_branches env d default w rest
    end.
Proof. reflexivity. Qed.

(** The branch TAKEN: first pattern matches; its payloads are pushed left-to-right
    (last payload = de Bruijn 0, the [push_env] convention). *)
Lemma wp_match_here : forall env scrut p body rest default payloads Q w,
  match_pat p (eval_val env scrut) = Some payloads ->
  wp (push_env payloads env) body Q w ->
  wp env (Match scrut ((p, body) :: rest) default) Q w.
Proof.
  intros env scrut p body rest default payloads Q w Hm HW.
  unfold wp in *; rewrite run_match_eq, try_branches_cons_eq, Hm; exact HW.
Qed.

(** Fall THROUGH: first pattern rejects; the Match continues with the remaining
    branches (first-match-wins). *)
Lemma wp_match_skip : forall env scrut p body rest default Q w,
  match_pat p (eval_val env scrut) = None ->
  wp env (Match scrut rest default) Q w ->
  wp env (Match scrut ((p, body) :: rest) default) Q w.
Proof.
  intros env scrut p body rest default Q w Hm HW.
  unfold wp in *; rewrite run_match_eq, try_branches_cons_eq, Hm.
  rewrite run_match_eq in HW; exact HW.
Qed.

(** No branch left: the mandatory default runs. *)
Lemma wp_match_default : forall env scrut default Q w,
  wp env default Q w -> wp env (Match scrut [] default) Q w.
Proof.
  intros env scrut default Q w H.
  unfold wp in *; rewrite run_match_eq, try_branches_nil_eq; exact H.
Qed.

(** [match_pat] inversion helpers, one per pattern (depth-1 grammar, adr-0008).
    First, reflection for the byte-string literal pattern. *)
Lemma ascii_eqb_eq : forall a b, ascii_eqb a b = true <-> a = b.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7] [b0 b1 b2 b3 b4 b5 b6 b7]; cbn.
  rewrite !andb_true_iff; split.
  - intros [[[[[[[H0 H1] H2] H3] H4] H5] H6] H7].
    repeat match goal with
           | H : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H
           end; subst; reflexivity.
  - intro H; injection H as -> -> -> -> -> -> -> ->.
    rewrite !Bool.eqb_reflx; repeat split.
Qed.

Lemma ascii_list_eqb_eq : forall xs ys, ascii_list_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [| x xs' IH]; destruct ys as [| y ys']; cbn; split; intro H;
    try reflexivity; try discriminate.
  - apply andb_true_iff in H as [H1 H2].
    apply ascii_eqb_eq in H1; apply IH in H2; subst; reflexivity.
  - injection H as -> ->.
    apply andb_true_iff; split; [apply ascii_eqb_eq | apply IH]; reflexivity.
Qed.

Lemma match_pat_unit_inv : forall d ps,
  match_pat PUnit d = Some ps -> d = DUnit /\ ps = [].
Proof. intros [] ps H; try discriminate; injection H as <-; auto. Qed.

Lemma match_pat_bool_inv : forall b d ps,
  match_pat (PBool b) d = Some ps -> d = DBool b /\ ps = [].
Proof.
  intros b [] ps H; try discriminate; cbn in H.
  destruct (Bool.eqb b b0) eqn:E; [| discriminate].
  apply Bool.eqb_prop in E; subst; injection H as <-; auto.
Qed.

Lemma match_pat_int_inv : forall z d ps,
  match_pat (PInt z) d = Some ps -> d = DInt z /\ ps = [].
Proof.
  intros z [] ps H; try discriminate; cbn in H.
  destruct (Z.eqb z z0) eqn:E; [| discriminate].
  apply Z.eqb_eq in E; subst; injection H as <-; auto.
Qed.

Lemma match_pat_bytes_inv : forall bs d ps,
  match_pat (PBytes bs) d = Some ps -> d = DBytes bs /\ ps = [].
Proof.
  intros bs [] ps H; try discriminate; cbn in H.
  destruct (ascii_list_eqb bs l) eqn:E; [| discriminate].
  apply ascii_list_eqb_eq in E; subst; injection H as <-; auto.
Qed.

Lemma match_pat_none_inv : forall d ps,
  match_pat PNone d = Some ps -> d = DNone /\ ps = [].
Proof. intros [] ps H; try discriminate; injection H as <-; auto. Qed.

Lemma match_pat_some_inv : forall d ps,
  match_pat PSome d = Some ps -> exists x, d = DSome x /\ ps = [x].
Proof. intros [] ps H; try discriminate; injection H as <-; eauto. Qed.

Lemma match_pat_pair_inv : forall d ps,
  match_pat PPair d = Some ps -> exists x y, d = DPair x y /\ ps = [x; y].
Proof. intros [] ps H; try discriminate; injection H as <-; eauto. Qed.

Lemma match_pat_tag_inv : forall z d ps,
  match_pat (PTag z) d = Some ps -> exists x, d = DTag z x /\ ps = [x].
Proof.
  intros z [] ps H; try discriminate; cbn in H.
  destruct (Z.eqb z z0) eqn:E; [| discriminate].
  apply Z.eqb_eq in E; subst; injection H as <-; eauto.
Qed.

(* ===== §6  Repeat: the index-carrying invariant rule ======================= *)

(** One-step twin equations for [repeat_loop] (Journal.v). *)
Lemma repeat_loop_zero_eq : forall env body w,
  repeat_loop env body 0 w = (ORet DUnit, w).
Proof. reflexivity. Qed.

Lemma repeat_loop_succ_eq : forall env body m w,
  repeat_loop env body (S m) w
  = match run env body w with
    | (ORet _, w1) => repeat_loop env body m w1
    | (OErr e, w1) => (OErr e, w1)
    end.
Proof. reflexivity. Qed.

(** The workhorse, by induction on the REMAINING fuel [m] with [i] iterations already
    done ([m + i = n]). The OErr escape: an aborting body iteration must land directly
    in Q. *)
Lemma repeat_loop_inv :
  forall env body (I : nat -> world -> Prop) (Q : outcome -> world -> Prop) (n : nat),
    (forall (i : nat) w0, (i < n)%nat -> I i w0 ->
       wp env body (fun o w1 => match o with
                                | ORet _ => I (S i) w1
                                | OErr e => Q (OErr e) w1
                                end) w0) ->
    (forall w1, I n w1 -> Q (ORet DUnit) w1) ->
    forall (m i : nat) w0, (m + i)%nat = n -> I i w0 ->
      let '(o, w') := repeat_loop env body m w0 in Q o w'.
Proof.
  intros env body I Q n Hbody Hend.
  induction m as [| m' IH]; intros i w0 Hmi HI.
  - rewrite repeat_loop_zero_eq; apply Hend.
    replace n with i by lia; exact HI.
  - rewrite repeat_loop_succ_eq.
    specialize (Hbody i w0 ltac:(lia) HI); unfold wp in Hbody.
    revert Hbody; destruct (run env body w0) as [[x | e] w1]; intro Hbody.
    + apply (IH (S i) w1); [lia | exact Hbody].
    + exact Hbody.
Qed.

(** THE Repeat rule (adr-0015 §Decision 2): supply an invariant indexed by the number
    of completed iterations; [I 0] holds initially, each non-aborting iteration steps
    the index, an aborting one escapes into Q, and [I n] must imply the loop's
    (ORet DUnit) postcondition. *)
Lemma wp_repeat_inv :
  forall env (n : nat) body (I : nat -> world -> Prop) Q w,
    I 0%nat w ->
    (forall (i : nat) w0, (i < n)%nat -> I i w0 ->
       wp env body (fun o w1 => match o with
                                | ORet _ => I (S i) w1
                                | OErr e => Q (OErr e) w1
                                end) w0) ->
    (forall w1, I n w1 -> Q (ORet DUnit) w1) ->
    wp env (Repeat n body) Q w.
Proof.
  intros env n body I Q w H0 Hbody Hend; unfold wp; rewrite run_repeat_eq.
  apply (repeat_loop_inv env body I Q n Hbody Hend n 0%nat w); [lia | exact H0].
Qed.

(* ===== §7  Fold: the prefix × accumulator invariant rule =================== *)

(** One-step twin equations for [fold_elems] (Journal.v). *)
Lemma fold_elems_nil_eq : forall env body acc w,
  fold_elems env body [] acc w = (ORet acc, w).
Proof. reflexivity. Qed.

Lemma fold_elems_step_eq : forall env body x xs acc w,
  fold_elems env body (x :: xs) acc w
  = match run (push_env [x; acc] env) body w with
    | (ORet acc', w1) => fold_elems env body xs acc' w1
    | (OErr e, w1)    => (OErr e, w1)
    end.
Proof. reflexivity. Qed.

(** The workhorse, by induction on the REMAINING elements with the processed prefix
    made explicit ([vs = pre ++ rest]). The body premise names the full split
    [vs = pre ++ x :: post] so invariants may look at position and remainder. *)
Lemma fold_elems_inv :
  forall env body (vs : list dval)
         (I : list dval -> dval -> world -> Prop) (Q : outcome -> world -> Prop),
    (forall pre x post acc w0,
       vs = pre ++ x :: post -> I pre acc w0 ->
       wp (push_env [x; acc] env) body
          (fun o w1 => match o with
                       | ORet acc' => I (pre ++ [x]) acc' w1
                       | OErr e    => Q (OErr e) w1
                       end) w0) ->
    (forall acc w1, I vs acc w1 -> Q (ORet acc) w1) ->
    forall rest pre acc w0, vs = pre ++ rest -> I pre acc w0 ->
      let '(o, w') := fold_elems env body rest acc w0 in Q o w'.
Proof.
  intros env body vs I Q Hbody Hend.
  induction rest as [| x rest' IH]; intros pre acc w0 Hsplit HI.
  - rewrite fold_elems_nil_eq; apply Hend.
    rewrite app_nil_r in Hsplit; subst pre; exact HI.
  - rewrite fold_elems_step_eq.
    specialize (Hbody pre x rest' acc w0 Hsplit HI); unfold wp in Hbody.
    revert Hbody; destruct (run (push_env [x; acc] env) body w0) as [[acc' | e] w1];
      intro Hbody.
    + apply (IH (pre ++ [x]) acc' w1); [rewrite <- app_assoc; exact Hsplit | exact Hbody].
    + exact Hbody.
Qed.

(** THE Fold rule (adr-0015 §Decision 2): the invariant relates the processed PREFIX
    of the (DList) scrutinee and the current accumulator; [init] establishes it at
    prefix []; each element step extends the prefix by one; an OErr from [init] or
    any iteration escapes into Q; [I vs acc] at the full list yields (ORet acc). *)
Lemma wp_fold_inv :
  forall env lst init body (vs : list dval)
         (I : list dval -> dval -> world -> Prop) Q w,
    eval_val env lst = DList vs ->
    wp env init (fun o w' => match o with
                             | ORet acc0 => I [] acc0 w'
                             | OErr e    => Q (OErr e) w'
                             end) w ->
    (forall pre x post acc w0,
       vs = pre ++ x :: post -> I pre acc w0 ->
       wp (push_env [x; acc] env) body
          (fun o w1 => match o with
                       | ORet acc' => I (pre ++ [x]) acc' w1
                       | OErr e    => Q (OErr e) w1
                       end) w0) ->
    (forall acc w1, I vs acc w1 -> Q (ORet acc) w1) ->
    wp env (Fold lst init body) Q w.
Proof.
  intros env lst init body vs I Q w Hlst Hinit Hbody Hend.
  unfold wp; rewrite run_fold_eq; unfold wp in Hinit.
  revert Hinit; destruct (run env init w) as [[acc0 | e] w']; intro Hinit.
  - rewrite Hlst.
    apply (fold_elems_inv env body vs I Q Hbody Hend vs [] acc0 w' eq_refl Hinit).
  - exact Hinit.
Qed.

(** Non-DList scrutinee: the fold is EMPTY — the result is exactly [init]'s result
    ([init]'s effects still happen exactly once; adr-0012 §Decision 2 posture). *)
Lemma wp_fold_empty : forall env lst init body Q w,
  match eval_val env lst with DList _ => False | _ => True end ->
  wp env init Q w ->
  wp env (Fold lst init body) Q w.
Proof.
  intros env lst init body Q w Hnl H; unfold wp in *; rewrite run_fold_eq.
  revert H; destruct (run env init w) as [[acc0 | e] w']; intro H; [| exact H].
  destruct (eval_val env lst); try exact H; contradiction.
Qed.

(** Print Assumptions footprint — each must say "Closed under the global context". *)
Print Assumptions wp_run.
Print Assumptions wp_conseq.
Print Assumptions wp_ret.
Print Assumptions wp_bind.
Print Assumptions wp_bind_err.
Print Assumptions wp_get.
Print Assumptions wp_get_live.
Print Assumptions wp_get_gone.
Print Assumptions wp_put.
Print Assumptions wp_delete.
Print Assumptions wp_get_deadline.
Print Assumptions wp_set_deadline_some.
Print Assumptions wp_set_deadline_none.
Print Assumptions wp_now.
Print Assumptions wp_ask.
Print Assumptions wp_throw.
Print Assumptions wp_trace.
Print Assumptions wp_journal.
Print Assumptions wp_cache_get.
Print Assumptions wp_cache_put.
Print Assumptions wp_prim.
Print Assumptions wp_prim_list_snoc.
Print Assumptions wp_match_here.
Print Assumptions wp_match_skip.
Print Assumptions wp_match_default.
Print Assumptions wp_repeat_inv.
Print Assumptions wp_fold_inv.
Print Assumptions wp_fold_empty.
