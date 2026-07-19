(** * ElabNs — ADR-0016 C2: the consolidation layer (store escaping + Cache + Journal).

    THE LAYER (adr-0016 §3 + §Corrections): Cache and Journal are NOT irreducible
    effects — they are proven implementations over the SAME expiring store the other
    ops use, made collision-free by TOTAL INJECTIVE KEY ESCAPING:
      user store keys  k  ↦  "u" ++ k
      cache keys       k  ↦  "c" ++ k     (entries stored deadline-free)
      the journal         ↦  "j"          (one chronological [DList] of [DPair now v])
    First-byte discrimination partitions the key space, so collisions are
    STRUCTURALLY impossible: no wf extension, no side condition — the theorem is
    unconditional, like C1's (adr-0016 §Corrections item 2; the earlier
    reserved-namespace-wf idea could not bound runtime-computed keys).

    The Cache elaboration is FAITHFUL, not null (§Corrections item 1): the null
    elaboration is unsound (put-then-get distinguishes it), so cache entries live in
    the store and every hit is reproduced exactly.

    THE THEOREM ([elab_ns_simulates]): for EVERY program, environment, and
    [nsrel]-related world pair, the elaborated program computes the SAME outcome,
    and the relation is preserved.  [nsrel] says: the mid store's [find] is exactly
    the three-armed view (u-arm = source store, c-arm = source cache entries with no
    deadline, j-arm = the encoded journal), the mid cache/journal are EMPTY (the
    elaborated code never touches them), and ctx/now/trace are equal.

    COMPOSITION ([elab_full]): [Elab.elab ∘ elab_ns] — the C1 Expiry layer then
    packs the consolidated store; mode K runs the composition over the kernel
    realizer set {Store_kernel, Time, Throw, Ask, Trace}: NO cache realizer, NO
    journal realizer, NO deadline logic ([elab_full_simulates]).

    Fragment discipline as in C1 (theories/Elab.v): arguments bound once at de
    Bruijn 0, zero shifting; [Prim PBytesConcat [VBytes prefix; k]] both escapes the
    key AND is the is-bytes shape test (mismatch is [DNone] — total prims);
    malformed-argument [Dstuck]s are reproduced bit-for-bit ([dstuck_val]).

    Anti-vacuity (adr-0005): cache put-then-get THROUGH the elaboration (the very
    program that kills the null elaboration — vm_compute), journal two-append order
    through the elaboration, a PREPENDING journal mutant observably rejected,
    explicit inhabitance, wf preservation with the all_programs vm_compute witness.
    Print Assumptions must read "Closed under the global context" throughout. *)

From Stdlib Require Import ZArith List String Ascii Bool Lia FMapFacts OrderedTypeEx.
From Rocqeteer Require Import EffIR Samples Journal Wf Elab.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation length := List.length.

Module NF := FMapFacts.WFacts_fun(String_as_OT)(M).

(* ===== §1  The escaped-key view and the relation ============================ *)

Definition pfx_u : ascii := "u"%char.
Definition pfx_c : ascii := "c"%char.
Definition pfx_j : ascii := "j"%char.

(** A cache binding consolidated into the store: deadline-free. *)
Definition cache_entry (v : dval) : entry := (v, None).

(** The journal consolidated into ONE store binding at key "j": a chronological
    [DList] of [DPair (DInt t) v] (the world's list is newest-first; [rev] is the
    chronological order [observe_full] exposes).  Empty journal = ABSENT binding
    (deterministic representation: the fragment writes only on append). *)
Definition journal_enc (js : list (Z * dval)) : option entry :=
  match js with
  | [] => None
  | _  => Some (DList (map (fun p => DPair (DInt (fst p)) (snd p)) (rev js)), None)
  end.

(** The three-armed view: what the consolidated store's [find] must return. *)
Definition ns_view (s : state) (ca : memo) (js : list (Z * dval)) (km : string)
  : option entry :=
  match km with
  | EmptyString => None
  | String ch rest =>
      if Ascii.eqb ch pfx_u then M.find rest s
      else if Ascii.eqb ch pfx_c then option_map cache_entry (M.find rest ca)
      else if Ascii.eqb ch pfx_j then
        match rest with EmptyString => journal_enc js | _ => None end
      else None
  end.

(** The consolidation relation: mid store = the view; mid cache/journal EMPTY
    (elaborated code never touches them); everything else equal. *)
Definition nsrel (w wm : world) : Prop :=
  (forall km, M.find km wm.(kv) = ns_view w.(kv) w.(cache) w.(journal) km)
  /\ wm.(ctx)     = w.(ctx)
  /\ wm.(now_ms)  = w.(now_ms)
  /\ wm.(trace)   = w.(trace)
  /\ wm.(cache)   = M.empty dval
  /\ wm.(journal) = [].

Definition sim_ns (r rm : outcome * world) : Prop :=
  fst rm = fst r /\ nsrel (snd r) (snd rm).

(* ===== §2  The fragments ==================================================== *)

(** User store ops: escape the key with the "u" prefix.  [PBytesConcat] is both
    the escape and the shape test (non-bytes key -> DNone -> the source Dstuck). *)
Definition ns_get (k : val) : tm :=
  Bind (Ret k)                                          (* kd *)
    (Bind (Prim PBytesConcat [VBytes [pfx_u]; VVar 0])  (* e·kd *)
       (Match (VVar 0)
          [(PNone, Ret dstuck_val)]
          (Perform OGet [VVar 0]))).

Definition ns_delete (k : val) : tm :=
  Bind (Ret k)
    (Bind (Prim PBytesConcat [VBytes [pfx_u]; VVar 0])
       (Match (VVar 0)
          [(PNone, Ret dstuck_val)]
          (Perform ODelete [VVar 0]))).

Definition ns_getdl (k : val) : tm :=
  Bind (Ret k)
    (Bind (Prim PBytesConcat [VBytes [pfx_u]; VVar 0])
       (Match (VVar 0)
          [(PNone, Ret dstuck_val)]
          (Perform OGetDeadline [VVar 0]))).

Definition ns_put (k v : val) : tm :=
  Bind (Ret (VPair k v))                                (* a = DPair kd vd *)
    (Match (VVar 0)
       [(PPair,                                         (* vd·kd·a *)
         Bind (Prim PBytesConcat [VBytes [pfx_u]; VVar 1])   (* e·vd·kd·a *)
           (Match (VVar 0)
              [(PNone, Ret dstuck_val)]
              (Perform OPut [VVar 0; VVar 1])))]
       (Ret dstuck_val)).                               (* unreachable: VPair is DPair *)

Definition ns_setdl (k dv : val) : tm :=
  Bind (Ret (VPair k dv))                               (* a = DPair kd dd *)
    (Match (VVar 0)
       [(PPair,                                         (* dd·kd·a *)
         Bind (Prim PBytesConcat [VBytes [pfx_u]; VVar 1])   (* e·dd·kd·a *)
           (Match (VVar 0)
              [(PNone, Ret dstuck_val)]
              (Perform OSetDeadline [VVar 0; VVar 1])))]
       (Ret dstuck_val)).

(** Cache, FAITHFUL and store-backed (adr-0016 §Corrections 1): a hit is a real
    read of the "c"-escaped binding — deadline-free, so liveness is vacuous. *)
Definition ns_cache_get (k : val) : tm :=
  Bind (Ret k)
    (Bind (Prim PBytesConcat [VBytes [pfx_c]; VVar 0])
       (Match (VVar 0)
          [(PNone, Ret dstuck_val)]
          (Perform OGet [VVar 0]))).

Definition ns_cache_put (k v : val) : tm :=
  Bind (Ret (VPair k v))
    (Match (VVar 0)
       [(PPair,                                         (* vd·kd·a *)
         Bind (Prim PBytesConcat [VBytes [pfx_c]; VVar 1])
           (Match (VVar 0)
              [(PNone, Ret dstuck_val)]
              (Perform OPut [VVar 0; VVar 1])))]
       (Ret dstuck_val)).

(** Journal: read the "j" list (absent = empty), snoc [DPair now v] (chronological
    order — [PListSnoc] appends at the END), write back.  Result is the [OPut]'s
    [DUnit], exactly the source's. *)
Definition ns_journal (v : val) : tm :=
  Bind (Ret v)                                          (* vd *)
    (Bind (Perform OGet [VBytes [pfx_j]])               (* r·vd *)
       (Bind (Match (VVar 0)
                [(PSome, Ret (VVar 0))]                 (* existing DList *)
                (Ret (VList [])))                       (* absent: empty *)
          (Bind (Perform ONow [])                       (* now·lst·r·vd *)
             (Bind (Prim PListSnoc [VVar 1; VPair (VVar 0) (VVar 3)])
                (Perform OPut [VBytes [pfx_j]; VVar 0]))))).

(* ===== §3  The elaboration ================================================== *)

(** One [Perform] site.  Cache/Journal ops at a WRONG arity are [Dstuck] with no
    world change at the source — elaborated to [Ret dstuck_val] directly, so the
    output program contains ZERO cache/journal ops.  Store ops at a wrong arity
    pass through (fallthrough [Dstuck] on both sides); non-consolidated ops pass
    through untouched. *)
Definition elab_perform_ns (o : op) (args : list val) : tm :=
  match o, args with
  | OGet,         [k]     => ns_get k
  | OPut,         [k; v]  => ns_put k v
  | ODelete,      [k]     => ns_delete k
  | OGetDeadline, [k]     => ns_getdl k
  | OSetDeadline, [k; dv] => ns_setdl k dv
  | OCacheGet,    [k]     => ns_cache_get k
  | OCachePut,    [k; v]  => ns_cache_put k v
  | OJournal,     [v]     => ns_journal v
  | OCacheGet, _ | OCachePut, _ | OJournal, _ => Ret dstuck_val
  | _, _                  => Perform o args
  end.

Fixpoint elab_ns (t : tm) : tm :=
  match t with
  | Ret v          => Ret v
  | Bind t1 t2     => Bind (elab_ns t1) (elab_ns t2)
  | Perform o args => elab_perform_ns o args
  | Match scrut branches default =>
      Match scrut
        ((fix eb (bs : list (pat * tm)) : list (pat * tm) :=
            match bs with
            | []                => []
            | (p, body) :: rest => (p, elab_ns body) :: eb rest
            end) branches)
        (elab_ns default)
  | Repeat n body  => Repeat n (elab_ns body)
  | Prim p args    => Prim p args
  | Fold lst init body => Fold lst (elab_ns init) (elab_ns body)
  end.

Definition elab_ns_branches :=
  fix eb (bs : list (pat * tm)) : list (pat * tm) :=
    match bs with
    | []                => []
    | (p, body) :: rest => (p, elab_ns body) :: eb rest
    end.

Lemma elab_ns_match_eq : forall scrut branches default,
  elab_ns (Match scrut branches default)
  = Match scrut (elab_ns_branches branches) (elab_ns default).
Proof. reflexivity. Qed.

(** THE mode-K artifact: the full tower — consolidation below, Expiry packing
    above (adr-0016 §Corrections 3). *)
Definition elab_full (t : tm) : tm := elab (elab_ns t).

Definition elab_full_programs : list (string * tm) :=
  map (fun nt => (fst nt, elab_full (snd nt))) all_programs.

(* ===== §4  View lemmas: the consolidated store under find/add/remove ======= *)

(** The view at each concrete prefix, by conversion (the [Ascii.eqb] tests are on
    literal characters).  Bare [cbn] is avoided near [M.find]/[M.add] — it unfolds
    them into [M.Raw] internals and the [FMapFacts] rewrites stop matching. *)
Lemma view_u : forall s ca js r,
  ns_view s ca js (String pfx_u r) = M.find r s.
Proof. reflexivity. Qed.

Lemma view_c : forall s ca js r,
  ns_view s ca js (String pfx_c r) = option_map cache_entry (M.find r ca).
Proof. reflexivity. Qed.

Lemma view_j0 : forall s ca js,
  ns_view s ca js (String pfx_j EmptyString) = journal_enc js.
Proof. reflexivity. Qed.

Lemma view_skip_u : forall s ca js k e km,
  km <> String pfx_u k ->
  ns_view (M.add k e s) ca js km = ns_view s ca js km.
Proof.
  intros s ca js k e km Hne.
  destruct km as [| ch rest]; [reflexivity |]; cbn [ns_view].
  destruct (Ascii.eqb ch pfx_u) eqn:Ec; [| reflexivity].
  apply Ascii.eqb_eq in Ec; subst ch.
  rewrite NF.add_o.
  destruct (NF.eq_dec k rest) as [e0 | n0]; [subst; congruence | reflexivity].
Qed.

Lemma nsrel_add_u : forall smid s ca js k e,
  (forall km, M.find km smid = ns_view s ca js km) ->
  forall km, M.find km (M.add (String pfx_u k) e smid)
             = ns_view (M.add k e s) ca js km.
Proof.
  intros smid s ca js k e Hv km.
  rewrite NF.add_o.
  destruct (NF.eq_dec (String pfx_u k) km) as [He | Hn].
  - subst km. rewrite view_u, NF.add_o.
    destruct (NF.eq_dec k k); [reflexivity | congruence].
  - rewrite (Hv km). symmetry. apply view_skip_u. congruence.
Qed.

Lemma view_skip_remove_u : forall s ca js k km,
  km <> String pfx_u k ->
  ns_view (M.remove k s) ca js km = ns_view s ca js km.
Proof.
  intros s ca js k km Hne.
  destruct km as [| ch rest]; [reflexivity |]; cbn [ns_view].
  destruct (Ascii.eqb ch pfx_u) eqn:Ec; [| reflexivity].
  apply Ascii.eqb_eq in Ec; subst ch.
  rewrite NF.remove_o.
  destruct (NF.eq_dec k rest) as [e0 | n0]; [subst; congruence | reflexivity].
Qed.

Lemma nsrel_remove_u : forall smid s ca js k,
  (forall km, M.find km smid = ns_view s ca js km) ->
  forall km, M.find km (M.remove (String pfx_u k) smid)
             = ns_view (M.remove k s) ca js km.
Proof.
  intros smid s ca js k Hv km.
  rewrite NF.remove_o.
  destruct (NF.eq_dec (String pfx_u k) km) as [He | Hn].
  - subst km. rewrite view_u, NF.remove_o.
    destruct (NF.eq_dec k k); [reflexivity | congruence].
  - rewrite (Hv km). symmetry. apply view_skip_remove_u. congruence.
Qed.

Lemma view_skip_c : forall s ca js k v km,
  km <> String pfx_c k ->
  ns_view s (M.add k v ca) js km = ns_view s ca js km.
Proof.
  intros s ca js k v km Hne.
  destruct km as [| ch rest]; [reflexivity |]; cbn [ns_view].
  destruct (Ascii.eqb ch pfx_u) eqn:Eu; [reflexivity |].
  destruct (Ascii.eqb ch pfx_c) eqn:Ec; [| reflexivity].
  apply Ascii.eqb_eq in Ec; subst ch.
  rewrite NF.add_o.
  destruct (NF.eq_dec k rest) as [e0 | n0]; [subst; congruence | reflexivity].
Qed.

Lemma nsrel_add_c : forall smid s ca js k v,
  (forall km, M.find km smid = ns_view s ca js km) ->
  forall km, M.find km (M.add (String pfx_c k) (cache_entry v) smid)
             = ns_view s (M.add k v ca) js km.
Proof.
  intros smid s ca js k v Hv km.
  rewrite NF.add_o.
  destruct (NF.eq_dec (String pfx_c k) km) as [He | Hn].
  - subst km. rewrite view_c, NF.add_o.
    destruct (NF.eq_dec k k); [reflexivity | congruence].
  - rewrite (Hv km). symmetry. apply view_skip_c. congruence.
Qed.

(** The journal write: appending [(n, vd)] snocs one encoded pair onto the stored
    chronological list, whatever the previous journal was. *)
Lemma journal_enc_snoc : forall js n vd,
  journal_enc ((n, vd) :: js)
  = Some (DList (map (fun p => DPair (DInt (fst p)) (snd p)) (rev js)
                 ++ [DPair (DInt n) vd]), None).
Proof.
  intros js n vd. unfold journal_enc.
  cbn [rev]. rewrite map_app. reflexivity.
Qed.

Lemma view_skip_j : forall s ca js js' km,
  km <> String pfx_j EmptyString ->
  ns_view s ca js' km = ns_view s ca js km.
Proof.
  intros s ca js js' km Hne.
  destruct km as [| ch rest]; [reflexivity |]; cbn [ns_view].
  destruct (Ascii.eqb ch pfx_u) eqn:Eu; [reflexivity |].
  destruct (Ascii.eqb ch pfx_c) eqn:Ec; [reflexivity |].
  destruct (Ascii.eqb ch pfx_j) eqn:Ej; [| reflexivity].
  apply Ascii.eqb_eq in Ej; subst ch.
  destruct rest; [congruence | reflexivity].
Qed.

Lemma nsrel_add_j : forall smid s ca js n vd,
  (forall km, M.find km smid = ns_view s ca js km) ->
  forall km,
    M.find km
      (M.add (String pfx_j EmptyString)
         ((DList (map (fun p => DPair (DInt (fst p)) (snd p)) (rev js)
                  ++ [DPair (DInt n) vd]), None) : entry) smid)
    = ns_view s ca ((n, vd) :: js) km.
Proof.
  intros smid s ca js n vd Hv km.
  rewrite NF.add_o.
  destruct (NF.eq_dec (String pfx_j EmptyString) km) as [He | Hn].
  - subst km. rewrite view_j0, journal_enc_snoc. reflexivity.
  - rewrite (Hv km). symmetry.
    apply (view_skip_j s ca js ((n, vd) :: js)). congruence.
Qed.

(* ===== §5  Fragment simulation lemmas ======================================= *)

(** Escaped keys reduce definitionally; kept as a rewrite target for robustness. *)
Lemma esc_key : forall c kb,
  string_of_list_ascii (c :: kb) = String c (string_of_list_ascii kb).
Proof. reflexivity. Qed.

Lemma ns_get_sim : forall k env w wm, nsrel w wm ->
  sim_ns (run env (Perform OGet [k]) w) (run env (ns_get k) wm).
Proof.
  intros k env w wm H.
  destruct H as (Hv & Hc & Hn & Ht & Hca & Hj).
  destruct w as [s c n tr ca j]; destruct wm as [sm cm nm trm cam jm].
  cbn in Hv, Hc, Hn, Ht, Hca, Hj; subst cm nm trm cam jm.
  unfold ns_get. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  (* DBytes: the escaped get reads the SAME entry through the view *)
  unfold find_live.
  rewrite (Hv (String pfx_u (string_of_list_ascii kb))), view_u.
  split; [reflexivity | repeat split; assumption].
Qed.

Lemma ns_delete_sim : forall k env w wm, nsrel w wm ->
  sim_ns (run env (Perform ODelete [k]) w) (run env (ns_delete k) wm).
Proof.
  intros k env w wm H.
  destruct H as (Hv & Hc & Hn & Ht & Hca & Hj).
  destruct w as [s c n tr ca j]; destruct wm as [sm cm nm trm cam jm].
  cbn in Hv, Hc, Hn, Ht, Hca, Hj; subst cm nm trm cam jm.
  unfold ns_delete. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  unfold find_live.
  rewrite (Hv (String pfx_u (string_of_list_ascii kb))), view_u.
  split; [reflexivity |].
  repeat split; try reflexivity; try assumption.
  apply (nsrel_remove_u _ _ _ _ _ Hv).
Qed.

Lemma ns_getdl_sim : forall k env w wm, nsrel w wm ->
  sim_ns (run env (Perform OGetDeadline [k]) w) (run env (ns_getdl k) wm).
Proof.
  intros k env w wm H.
  destruct H as (Hv & Hc & Hn & Ht & Hca & Hj).
  destruct w as [s c n tr ca j]; destruct wm as [sm cm nm trm cam jm].
  cbn in Hv, Hc, Hn, Ht, Hca, Hj; subst cm nm trm cam jm.
  unfold ns_getdl. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  unfold find_live.
  rewrite (Hv (String pfx_u (string_of_list_ascii kb))), view_u.
  split; [reflexivity | repeat split; assumption].
Qed.

Lemma ns_put_sim : forall k v env w wm, nsrel w wm ->
  sim_ns (run env (Perform OPut [k; v]) w) (run env (ns_put k v) wm).
Proof.
  intros k v env w wm H.
  destruct H as (Hv & Hc & Hn & Ht & Hca & Hj).
  destruct w as [s c n tr ca j]; destruct wm as [sm cm nm trm cam jm].
  cbn in Hv, Hc, Hn, Ht, Hca, Hj; subst cm nm trm cam jm.
  unfold ns_put. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  split; [reflexivity |].
  repeat split; try reflexivity; try assumption.
  apply (nsrel_add_u _ _ _ _ _ (eval_val env v, None) Hv).
Qed.

Lemma ns_setdl_sim : forall k dv env w wm, nsrel w wm ->
  sim_ns (run env (Perform OSetDeadline [k; dv]) w) (run env (ns_setdl k dv) wm).
Proof.
  intros k dv env w wm H.
  destruct H as (Hv & Hc & Hn & Ht & Hca & Hj).
  destruct w as [s c n tr ca j]; destruct wm as [sm cm nm trm cam jm].
  cbn in Hv, Hc, Hn, Ht, Hca, Hj; subst cm nm trm cam jm.
  unfold ns_setdl. cbn.
  destruct (eval_val env k) as [| b | z | | dvk | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (destruct (eval_val env dv) as [| b2 | z2 | | dp | e1 e2 | bs2 | tg2 tv2 | ds2 |]
           eqn:Edv; cbn;
         (split; [reflexivity | repeat split; assumption])).
  (* DBytes key: the mid op dispatches on the SAME deadline argument *)
  destruct (eval_val env dv) as [| b2 | z2 | | dp | e1 e2 | bs2 | tg2 tv2 | ds2 |]
    eqn:Edv; cbn;
    try (split; [reflexivity | repeat split; assumption]).
  - (* dd = DNone *)
    unfold find_live.
    rewrite (Hv (String pfx_u (string_of_list_ascii kb))), view_u.
    destruct (M.find (string_of_list_ascii kb) s) as [[v0 dl] |] eqn:Ef; cbn.
    + destruct (live n (v0, dl)) eqn:El; cbn;
        split; [reflexivity | repeat split; try reflexivity; try assumption;
                              apply (nsrel_add_u _ _ _ _ _ (v0, None) Hv) |
                reflexivity | repeat split; assumption].
    + split; [reflexivity | repeat split; assumption].
  - (* dd = DSome dp: only DInt payloads write *)
    destruct dp as [| b3 | d' | | dp' | f1 f2 | bs3 | tg3 tv3 | ds3 |]; cbn;
      try (split; [reflexivity | repeat split; assumption]).
    unfold find_live.
    rewrite (Hv (String pfx_u (string_of_list_ascii kb))), view_u.
    destruct (M.find (string_of_list_ascii kb) s) as [[v0 dl] |] eqn:Ef; cbn.
    + destruct (live n (v0, dl)) eqn:El; cbn;
        split; [reflexivity | repeat split; try reflexivity; try assumption;
                              apply (nsrel_add_u _ _ _ _ _ (v0, Some d') Hv) |
                reflexivity | repeat split; assumption].
    + split; [reflexivity | repeat split; assumption].
Qed.

Lemma ns_cache_get_sim : forall k env w wm, nsrel w wm ->
  sim_ns (run env (Perform OCacheGet [k]) w) (run env (ns_cache_get k) wm).
Proof.
  intros k env w wm H.
  destruct H as (Hv & Hc & Hn & Ht & Hca & Hj).
  destruct w as [s c n tr ca j]; destruct wm as [sm cm nm trm cam jm].
  cbn in Hv, Hc, Hn, Ht, Hca, Hj; subst cm nm trm cam jm.
  unfold ns_cache_get. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  (* DBytes: the "c"-escaped binding IS the cache entry, deadline-free *)
  unfold find_live.
  rewrite (Hv (String pfx_c (string_of_list_ascii kb))), view_c.
  destruct (M.find (string_of_list_ascii kb) ca) as [v |]; cbn;
    split; [reflexivity | repeat split; assumption |
            reflexivity | repeat split; assumption].
Qed.

Lemma ns_cache_put_sim : forall k v env w wm, nsrel w wm ->
  sim_ns (run env (Perform OCachePut [k; v]) w) (run env (ns_cache_put k v) wm).
Proof.
  intros k v env w wm H.
  destruct H as (Hv & Hc & Hn & Ht & Hca & Hj).
  destruct w as [s c n tr ca j]; destruct wm as [sm cm nm trm cam jm].
  cbn in Hv, Hc, Hn, Ht, Hca, Hj; subst cm nm trm cam jm.
  unfold ns_cache_put. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  split; [reflexivity |].
  repeat split; try reflexivity; try assumption.
  apply (nsrel_add_c _ _ _ _ _ (eval_val env v) Hv).
Qed.

Lemma ns_journal_sim : forall v env w wm, nsrel w wm ->
  sim_ns (run env (Perform OJournal [v]) w) (run env (ns_journal v) wm).
Proof.
  intros v env w wm H.
  destruct H as (Hv & Hc & Hn & Ht & Hca & Hj).
  destruct w as [s c n tr ca j]; destruct wm as [sm cm nm trm cam jm].
  cbn in Hv, Hc, Hn, Ht, Hca, Hj; subst cm nm trm cam jm.
  unfold ns_journal. cbn.
  unfold find_live.
  rewrite (Hv (String pfx_j EmptyString)), view_j0.
  destruct j as [| p js']; cbn.
  - (* empty journal: absent binding, start from [] *)
    split; [reflexivity |].
    repeat split; try reflexivity; try assumption.
    apply (nsrel_add_j _ _ _ [] _ _ Hv).
  - (* nonempty: read the chronological list, snoc, write back *)
    split; [reflexivity |].
    repeat split; try reflexivity; try assumption.
    apply (nsrel_add_j _ _ _ (p :: js') _ _ Hv).
Qed.

(* ===== §6  The Perform dispatch and the construct twins ===================== *)

(** Pass-through and Ret-dstuck cases: ops that never touch store/cache/journal,
    store ops at a wrong arity (fallthrough [Dstuck] on both sides), and
    cache/journal ops at a wrong arity (source [Dstuck] with no world change,
    elaborated to [Ret dstuck_val]). *)
Local Ltac ns_pass H w wm :=
  destruct H as (Hv & Hc & Hn & Ht & Hca & Hj);
  destruct w; destruct wm;
  cbn in Hv, Hc, Hn, Ht, Hca, Hj; subst;
  cbn;
  repeat (match goal with
          | |- context [eval_val ?e ?v] => destruct (eval_val e v)
          | |- context [match ?x with
                        | DUnit => _ | DBool _ => _ | DInt _ => _ | DNone => _
                        | DSome _ => _ | DPair _ _ => _ | DBytes _ => _
                        | DTag _ _ => _ | DList _ => _ | Dstuck => _
                        end] => destruct x
          | |- context [map (eval_val ?e) ?l] => destruct l
          end; cbn);
  (split; [reflexivity | repeat split; try assumption; reflexivity]).

Lemma elab_perform_ns_sim : forall o args env w wm, nsrel w wm ->
  sim_ns (run env (Perform o args) w) (run env (elab_perform_ns o args) wm).
Proof.
  intros o args env w wm H.
  destruct o.
  - destruct args as [| k [| a2 args']];
      [ ns_pass H w wm | apply ns_get_sim; exact H | ns_pass H w wm ].
  - destruct args as [| k [| v [| a3 args']]];
      [ ns_pass H w wm | ns_pass H w wm
      | apply ns_put_sim; exact H | ns_pass H w wm ].
  - destruct args as [| k [| a2 args']];
      [ ns_pass H w wm | apply ns_delete_sim; exact H | ns_pass H w wm ].
  - destruct args as [| k [| a2 args']];
      [ ns_pass H w wm | apply ns_getdl_sim; exact H | ns_pass H w wm ].
  - destruct args as [| k [| dv [| a3 args']]];
      [ ns_pass H w wm | ns_pass H w wm
      | apply ns_setdl_sim; exact H | ns_pass H w wm ].
  - (* ONow *)   ns_pass H w wm.
  - (* OThrow *) ns_pass H w wm.
  - (* OAsk *)   ns_pass H w wm.
  - (* OTrace *) ns_pass H w wm.
  - (* OCacheGet *)
    destruct args as [| k [| a2 args']];
      [ ns_pass H w wm | apply ns_cache_get_sim; exact H | ns_pass H w wm ].
  - (* OCachePut *)
    destruct args as [| k [| v [| a3 args']]];
      [ ns_pass H w wm | ns_pass H w wm
      | apply ns_cache_put_sim; exact H | ns_pass H w wm ].
  - (* OJournal *)
    destruct args as [| v [| a2 args']];
      [ ns_pass H w wm | apply ns_journal_sim; exact H | ns_pass H w wm ].
Qed.

Lemma try_branches_ns_sim :
  forall branches env d default w wm,
    Forall (fun pb => forall env' w' wm', nsrel w' wm' ->
              sim_ns (run env' (snd pb) w') (run env' (elab_ns (snd pb)) wm')) branches ->
    (forall env' w' wm', nsrel w' wm' ->
        sim_ns (run env' default w') (run env' (elab_ns default) wm')) ->
    nsrel w wm ->
    sim_ns (try_branches env d default w branches)
           (try_branches env d (elab_ns default) wm (elab_ns_branches branches)).
Proof.
  induction branches as [| [p body] rest IH]; intros env d default w wm HF Hdef H.
  - cbn. apply Hdef; exact H.
  - inversion HF as [| ? ? Hbody HFrest]; subst.
    cbn. destruct (match_pat p d) as [payloads |].
    + apply Hbody; exact H.
    + apply IH; assumption.
Qed.

Lemma repeat_loop_ns_sim :
  forall env body,
    (forall env' w' wm', nsrel w' wm' ->
        sim_ns (run env' body w') (run env' (elab_ns body) wm')) ->
    forall n w wm, nsrel w wm ->
      sim_ns (repeat_loop env body n w) (repeat_loop env (elab_ns body) n wm).
Proof.
  intros env body Hb; induction n as [| m IH]; intros w wm H; cbn.
  - split; [reflexivity | exact H].
  - pose proof (Hb env w wm H) as Hstep.
    destruct (run env body w) as [[x | e] w1];
      destruct (run env (elab_ns body) wm) as [[xm | em] wm1];
      destruct Hstep as [Hfst Hw]; cbn in Hfst, Hw; try discriminate.
    + apply IH; exact Hw.
    + injection Hfst as ->. split; [reflexivity | exact Hw].
Qed.

Lemma fold_elems_ns_sim :
  forall env body,
    (forall env' w' wm', nsrel w' wm' ->
        sim_ns (run env' body w') (run env' (elab_ns body) wm')) ->
    forall vs acc w wm, nsrel w wm ->
      sim_ns (fold_elems env body vs acc w) (fold_elems env (elab_ns body) vs acc wm).
Proof.
  intros env body Hb; induction vs as [| x xs IH]; intros acc w wm H.
  - cbn. split; [reflexivity | exact H].
  - rewrite !fold_elems_cons.
    pose proof (Hb (push_env [x; acc] env) w wm H) as Hstep.
    destruct (run (push_env [x; acc] env) body w) as [[acc' | e] w1];
      destruct (run (push_env [x; acc] env) (elab_ns body) wm) as [[accm | em] wm1];
      destruct Hstep as [Hfst Hw]; cbn in Hfst, Hw; try discriminate.
    + injection Hfst as ->. apply IH; exact Hw.
    + injection Hfst as ->. split; [reflexivity | exact Hw].
Qed.

(* ===== §7  THE CONSOLIDATION THEOREM (adr-0016 §Corrections 3) ============== *)

(** For EVERY program, environment, and [nsrel]-related world pair: the elaborated
    program computes the SAME outcome with Cache and Journal consolidated into the
    escaped store, and the relation is preserved.  Unconditional — key escaping
    makes collisions structurally impossible, so there is no namespace side
    condition, and malformed-argument [Dstuck]s are reproduced exactly. *)
Theorem elab_ns_simulates : forall t env w wm, nsrel w wm ->
  sim_ns (run env t w) (run env (elab_ns t) wm).
Proof.
  apply (tm_ind_strong (fun t => forall env w wm, nsrel w wm ->
           sim_ns (run env t w) (run env (elab_ns t) wm))).
  - intros v env w wm H; cbn. split; [reflexivity | exact H].
  - intros t1 t2 IH1 IH2 env w wm H; cbn.
    pose proof (IH1 env w wm H) as Hstep.
    destruct (run env t1 w) as [[x | e] w1];
      destruct (run env (elab_ns t1) wm) as [[xm | em] wm1];
      destruct Hstep as [Hfst Hw]; cbn in Hfst, Hw; try discriminate.
    + injection Hfst as ->. apply IH2; exact Hw.
    + injection Hfst as ->. split; [reflexivity | exact Hw].
  - intros o args env w wm H. apply elab_perform_ns_sim; exact H.
  - intros scrut branches default HF Hdef env w wm H.
    rewrite elab_ns_match_eq, !run_match_eq.
    apply try_branches_ns_sim; assumption.
  - intros n body IHb env w wm H.
    cbn [elab_ns]. rewrite !run_repeat_eq.
    apply repeat_loop_ns_sim; assumption.
  - intros p args env w wm H; cbn. split; [reflexivity | exact H].
  - intros lst init body IHi IHb env w wm H.
    cbn [elab_ns]. rewrite !run_fold_eq.
    pose proof (IHi env w wm H) as Hstep.
    destruct (run env init w) as [[acc0 | e] w1];
      destruct (run env (elab_ns init) wm) as [[accm | em] wm1];
      destruct Hstep as [Hfst Hw]; cbn in Hfst, Hw; try discriminate.
    + injection Hfst as ->.
      destruct (eval_val env lst); try (split; [reflexivity | exact Hw]).
      apply fold_elems_ns_sim; assumption.
    + injection Hfst as ->. split; [reflexivity | exact Hw].
Qed.

(* ===== §8  THE FULL TOWER: composition with the Expiry layer ================ *)

(** Mode K end-to-end (adr-0016 §Corrections 3): consolidate (this file), then pack
    (theories/Elab.v).  For any source world, any [nsrel]-related mid world, and any
    [wrel]-related kernel world: same outcome, relations preserved level by level. *)
Theorem elab_full_simulates : forall t env w wm wk,
  nsrel w wm -> wrel wm wk ->
  fst (run env (elab_full t) wk) = fst (run env t w)
  /\ nsrel (snd (run env t w)) (snd (run env (elab_ns t) wm))
  /\ wrel (snd (run env (elab_ns t) wm)) (snd (run env (elab_full t) wk)).
Proof.
  intros t env w wm wk Hns Hw.
  pose proof (elab_ns_simulates t env w wm Hns) as [Hf1 Hr1].
  pose proof (elab_simulates (elab_ns t) env wm wk Hw) as [Hf2 Hr2].
  unfold elab_full.
  split; [rewrite Hf2; exact Hf1 | split; [exact Hr1 | exact Hr2]].
Qed.

(** Closed-program form from the canonical initial worlds: an empty source world
    consolidates to an empty mid world and packs to an empty kernel world. *)
Corollary elab_full_run_top : forall t c now,
  fst (run [] (elab_full t) (init_world c now)) = fst (run_top c now t).
Proof.
  intros t c now.
  destruct (elab_full_simulates t [] (init_world c now) (init_world c now)
              (init_world c now)) as (Hf & _ & _).
  - repeat split; try reflexivity. intro km.
    rewrite NF.empty_o.
    destruct km as [| ch rest]; cbn [ns_view]; [reflexivity |].
    destruct (Ascii.eqb ch pfx_u); [now rewrite NF.empty_o |].
    destruct (Ascii.eqb ch pfx_c); [now rewrite NF.empty_o |].
    destruct (Ascii.eqb ch pfx_j); [destruct rest |]; reflexivity.
  - repeat split; reflexivity.
  - exact Hf.
Qed.

(* ===== §9  wf preservation ================================================== *)

Lemma wf_ns_get : forall depth k,
  wf_val depth k = true -> wf_tm depth (ns_get k) = true.
Proof. intros depth k H; cbn; rewrite H; reflexivity. Qed.

Lemma wf_ns_delete : forall depth k,
  wf_val depth k = true -> wf_tm depth (ns_delete k) = true.
Proof. intros depth k H; cbn; rewrite H; reflexivity. Qed.

Lemma wf_ns_getdl : forall depth k,
  wf_val depth k = true -> wf_tm depth (ns_getdl k) = true.
Proof. intros depth k H; cbn; rewrite H; reflexivity. Qed.

Lemma wf_ns_put : forall depth k v,
  wf_val depth k = true -> wf_val depth v = true ->
  wf_tm depth (ns_put k v) = true.
Proof. intros depth k v Hk Hv; cbn; rewrite Hk, Hv; reflexivity. Qed.

Lemma wf_ns_setdl : forall depth k dv,
  wf_val depth k = true -> wf_val depth dv = true ->
  wf_tm depth (ns_setdl k dv) = true.
Proof. intros depth k dv Hk Hv; cbn; rewrite Hk, Hv; reflexivity. Qed.

Lemma wf_ns_cache_get : forall depth k,
  wf_val depth k = true -> wf_tm depth (ns_cache_get k) = true.
Proof. intros depth k H; cbn; rewrite H; reflexivity. Qed.

Lemma wf_ns_cache_put : forall depth k v,
  wf_val depth k = true -> wf_val depth v = true ->
  wf_tm depth (ns_cache_put k v) = true.
Proof. intros depth k v Hk Hv; cbn; rewrite Hk, Hv; reflexivity. Qed.

Lemma wf_ns_journal : forall depth v,
  wf_val depth v = true -> wf_tm depth (ns_journal v) = true.
Proof. intros depth v H; cbn; rewrite H; reflexivity. Qed.

Lemma wf_elab_perform_ns : forall depth o args,
  Nat.eqb (length args) (op_arity o) && forallb (wf_val depth) args = true ->
  wf_tm depth (elab_perform_ns o args) = true.
Proof.
  intros depth o args H.
  destruct o; cbn in H;
    destruct args as [| a1 [| a2 [| a3 rest]]]; try discriminate; cbn in H;
    repeat match goal with
           | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
           end;
    cbn; try rewrite ?H, ?H0, ?H1; try reflexivity;
    auto using wf_ns_get, wf_ns_put, wf_ns_delete, wf_ns_getdl, wf_ns_setdl,
               wf_ns_cache_get, wf_ns_cache_put, wf_ns_journal.
Qed.

Lemma wf_elab_ns_branches : forall branches depth,
  Forall (fun pb => forall depth',
            wf_tm depth' (snd pb) = true -> wf_tm depth' (elab_ns (snd pb)) = true)
         branches ->
  wf_branches depth branches = true ->
  wf_branches depth (elab_ns_branches branches) = true.
Proof.
  induction branches as [| [p body] rest IH]; intros depth HF Hwb; cbn in *.
  - reflexivity.
  - inversion HF as [| ? ? Hbody HFrest]; subst; cbn [snd] in Hbody.
    apply andb_true_iff in Hwb as [Hb Hr].
    rewrite (Hbody _ Hb). apply IH; assumption.
Qed.

Theorem wf_elab_ns : forall t depth,
  wf_tm depth t = true -> wf_tm depth (elab_ns t) = true.
Proof.
  apply (tm_ind_strong (fun t => forall depth,
           wf_tm depth t = true -> wf_tm depth (elab_ns t) = true)).
  - intros v depth H; exact H.
  - intros t1 t2 IH1 IH2 depth H; cbn in H |- *.
    apply andb_true_iff in H as [H1 H2].
    rewrite (IH1 _ H1), (IH2 _ H2). reflexivity.
  - intros o args depth H. apply wf_elab_perform_ns. exact H.
  - intros scrut branches default HF Hdef depth H.
    rewrite wf_tm_match_eq in H.
    apply andb_true_iff in H as [H1 Hwd];
      apply andb_true_iff in H1 as [Hs Hwb].
    rewrite elab_ns_match_eq, wf_tm_match_eq.
    rewrite Hs, (wf_elab_ns_branches _ _ HF Hwb), (Hdef _ Hwd). reflexivity.
  - intros n body IHb depth H; cbn in H |- *. apply IHb; exact H.
  - intros p args depth H; exact H.
  - intros lst init body IHi IHb depth H; cbn in H |- *.
    apply andb_true_iff in H as [H1 Hb]; apply andb_true_iff in H1 as [Hl Hi].
    rewrite Hl, (IHi _ Hi), (IHb _ Hb). reflexivity.
Qed.

(** The composed tower preserves wf — the codegen gate accepts mode-K programs. *)
Theorem wf_elab_full : forall t depth,
  wf_tm depth t = true -> wf_tm depth (elab_full t) = true.
Proof.
  intros t depth H. unfold elab_full. apply wf_elab, wf_elab_ns; exact H.
Qed.

(* ===== §10  Anti-vacuity (adr-0005) ========================================= *)

Definition ckey : list ascii := list_ascii_of_string "m".

(** The program that KILLS the null cache elaboration (adr-0016 §Corrections 1):
    put then get must see the cached value. *)
Definition cache_probe : tm :=
  Bind (Perform OCachePut [VBytes ckey; VInt 1])
       (Perform OCacheGet [VBytes ckey]).

Theorem cache_probe_source :
  fst (run_top DUnit 0 cache_probe) = ORet (DSome (DInt 1)).
Proof. vm_compute. reflexivity. Qed.

(** The FAITHFUL elaboration reproduces the hit — through the FULL tower, over the
    kernel fragment. *)
Theorem cache_probe_full :
  fst (run [] (elab_full cache_probe) (init_world DUnit 0)) = ORet (DSome (DInt 1)).
Proof. vm_compute. reflexivity. Qed.

(** Journal order through the consolidation: two appends store the CHRONOLOGICAL
    list at "j" — and survive the Expiry packing on top. *)
Definition journal_probe : tm :=
  Bind (Perform OJournal [VInt 1]) (Perform OJournal [VInt 2]).

Theorem journal_probe_source :
  journal (snd (run_top DUnit 5 journal_probe)) = [(5, DInt 2); (5, DInt 1)].
Proof. vm_compute. reflexivity. Qed.

Theorem journal_probe_mid :
  M.find (String pfx_j EmptyString)
    (kv (snd (run [] (elab_ns journal_probe) (init_world DUnit 5))))
  = Some (DList [DPair (DInt 5) (DInt 1); DPair (DInt 5) (DInt 2)], None).
Proof. vm_compute. reflexivity. Qed.

Theorem journal_probe_full :
  M.find (String pfx_j EmptyString)
    (kv (snd (run [] (elab_full journal_probe) (init_world DUnit 5))))
  = Some (DPair (DList [DPair (DInt 5) (DInt 1); DPair (DInt 5) (DInt 2)]) DNone,
          None).
Proof. vm_compute. reflexivity. Qed.

(** MUTANT consolidation (the adr-0005 companion): the NULL cache (always miss,
    forget puts) and the FORGETFUL journal (drops history, keeps only the newest
    entry) — exactly the two shortcuts §Corrections rules out. *)
Definition elab_perform_ns_mutant (o : op) (args : list val) : tm :=
  match o, args with
  | OCacheGet,  [_k]    => Ret VNone                       (* MUTANT: always miss *)
  | OCachePut,  [_k; _] => Ret VUnit                       (* MUTANT: forget *)
  | OJournal,   [v]     =>                                 (* MUTANT: drop history *)
      Bind (Ret v)
        (Bind (Perform ONow [])
           (Bind (Prim PListSnoc [VList []; VPair (VVar 0) (VVar 1)])
              (Perform OPut [VBytes [pfx_j]; VVar 0])))
  | _, _ => elab_perform_ns o args
  end.

Fixpoint elab_ns_mutant (t : tm) : tm :=
  match t with
  | Ret v          => Ret v
  | Bind t1 t2     => Bind (elab_ns_mutant t1) (elab_ns_mutant t2)
  | Perform o args => elab_perform_ns_mutant o args
  | Match scrut branches default =>
      Match scrut
        ((fix eb (bs : list (pat * tm)) : list (pat * tm) :=
            match bs with
            | []                => []
            | (p, body) :: rest => (p, elab_ns_mutant body) :: eb rest
            end) branches)
        (elab_ns_mutant default)
  | Repeat n body  => Repeat n (elab_ns_mutant body)
  | Prim p args    => Prim p args
  | Fold lst init body => Fold lst (elab_ns_mutant init) (elab_ns_mutant body)
  end.

(** The null cache is observably WRONG on the probe (the §Corrections witness)... *)
Theorem mutant_cache_rejected :
  fst (run [] (elab_ns_mutant cache_probe) (init_world DUnit 0))
  <> fst (run_top DUnit 0 cache_probe).
Proof. vm_compute. intro H; discriminate H. Qed.

(** ... the forgetful journal loses the first entry... *)
Theorem mutant_journal_rejected :
  M.find (String pfx_j EmptyString)
    (kv (snd (run [] (elab_ns_mutant journal_probe) (init_world DUnit 5))))
  <> M.find (String pfx_j EmptyString)
       (kv (snd (run [] (elab_ns journal_probe) (init_world DUnit 5)))).
Proof. vm_compute. intro H; discriminate H. Qed.

(** ... while agreeing on cache/journal-free programs: the mutations are PLAUSIBLE
    (the store consolidation is untouched), so the probes carry the rejection. *)
Theorem mutant_plausible_on_store :
  fst (run [] (elab_ns_mutant prog0) (init_world DUnit 0))
  = fst (run_top DUnit 0 prog0).
Proof. vm_compute. reflexivity. Qed.

(** The empty pair is related — the base of the chained-update witness below. *)
Lemma view_empty : forall km,
  M.find km (M.empty entry)
  = ns_view (M.empty entry) (M.empty dval) [] km.
Proof.
  intro km. rewrite NF.empty_o.
  destruct km as [| ch rest]; cbn [ns_view]; [reflexivity |].
  destruct (Ascii.eqb ch pfx_u); [now rewrite NF.empty_o |].
  destruct (Ascii.eqb ch pfx_c); [now rewrite NF.empty_o |].
  destruct (Ascii.eqb ch pfx_j); [destruct rest |]; reflexivity.
Qed.

(** Explicit-witness inhabitance: a related pair with NONEMPTY store, cache, AND
    journal, built by chaining the §4 update lemmas from the empty pair — and the
    elaborated cache get REALLY reads through the consolidation on it. *)
Theorem nsrel_inhabited :
  exists w wm,
    nsrel w wm
    /\ w.(cache) <> M.empty dval
    /\ w.(journal) <> []
    /\ fst (run [] (elab_ns (Perform OCacheGet [VBytes ckey])) wm)
       = ORet (DSome (DInt 9)).
Proof.
  set (s1 := M.add "k"%string (DInt 7, Some 100) (M.empty entry)).
  set (ca1 := M.add (string_of_list_ascii ckey) (DInt 9) (M.empty dval)).
  set (js1 := [(40, DInt 3)]).
  set (sm := M.add (String pfx_u "k"%string) (DInt 7, Some 100)
               (M.add (String pfx_c (string_of_list_ascii ckey)) (cache_entry (DInt 9))
                  (M.add (String pfx_j EmptyString)
                     ((DList [DPair (DInt 40) (DInt 3)], None) : entry)
                     (M.empty entry)))).
  assert (Hview : forall km, M.find km sm = ns_view s1 ca1 js1 km).
  { intro km. unfold sm, s1, ca1, js1.
    apply nsrel_add_u. intro km1.
    apply nsrel_add_c. intro km2.
    apply (nsrel_add_j _ _ _ [] 40 (DInt 3)). intro km3.
    apply view_empty. }
  exists (mkWorld s1 DUnit 50 [] ca1 js1).
  exists (mkWorld sm DUnit 50 [] (M.empty dval) []).
  repeat split; try reflexivity.
  (* remaining: the view, the two nonemptiness witnesses (the elaborated-hit
     equation was closed by reflexivity's conversion) *)
  - exact Hview.
  - (* nonempty cache *)
    cbn. intro He.
    assert (H9 : M.find (string_of_list_ascii ckey) ca1 = Some (DInt 9)).
    { unfold ca1. rewrite NF.add_o.
      destruct (NF.eq_dec (string_of_list_ascii ckey) (string_of_list_ascii ckey));
        [reflexivity | congruence]. }
    rewrite He, NF.empty_o in H9. discriminate.
  - (* nonempty journal *)
    cbn. unfold js1. discriminate.
Qed.

(** The composed single-source list is wf — the codegen gate accepts every mode-K
    program (vm_compute companion of [wf_elab_full]). *)
Theorem elab_full_all_programs_wf :
  forallb (fun nt => wf_tm 0%nat (snd nt)) elab_full_programs = true.
Proof. vm_compute. reflexivity. Qed.

(* ===== §11  Print Assumptions =============================================== *)

(** Each must read "Closed under the global context". *)
Print Assumptions elab_ns_simulates.
Print Assumptions elab_full_simulates.
Print Assumptions elab_full_run_top.
Print Assumptions wf_elab_ns.
Print Assumptions wf_elab_full.
Print Assumptions cache_probe_source.
Print Assumptions cache_probe_full.
Print Assumptions journal_probe_source.
Print Assumptions journal_probe_mid.
Print Assumptions journal_probe_full.
Print Assumptions mutant_cache_rejected.
Print Assumptions mutant_journal_rejected.
Print Assumptions mutant_plausible_on_store.
Print Assumptions nsrel_inhabited.
Print Assumptions elab_full_all_programs_wf.
