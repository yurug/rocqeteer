(** * Elab — ADR-0016 C1: the Expiry elaboration (the first effect-tower layer).

    THE TOWER (adr-0016 §2-3): the expiring-store surface — deadline liveness inside
    [OGet]/[ODelete], [OGetDeadline], [OSetDeadline] — is NOT an irreducible effect: it
    is a proven implementation over the KERNEL fragment (plain never-expiring store +
    [ONow]).  [elab : tm -> tm] macro-expands each store op into a kernel program that
    stores PACKED entries — the value [DPair v dl] where [dl] is the dval encoding of
    the optional deadline — under a kernel binding that never expires (deadline [None]).
    The kernel ops in the output are the SAME EffIR ops ([OGet]/[OPut]/[ODelete]),
    used only on deadline-free bindings, where [handle_store]'s liveness test is
    vacuous: the IR gains ZERO constructs (invariant 1 — one EffIR, two backends).

    THE THEOREM ([elab_simulates]): running [elab t] on a PACKED world produces the
    SAME outcome as running [t] on the source world, with final stores related
    entry-wise by packing ([M.Equal], the map-observational equality) and every other
    world field EQUAL — for EVERY program, EVERY environment, EVERY world (no wf
    side condition: malformed-argument [Dstuck]s are reproduced bit-for-bit).
    Corollaries give the closed-program form and the observe-level reading.
    Lazy-expiry freedom is absorbed by the relation: a dead source binding is packed
    as a present-but-dead kernel binding; both are invisible to every op.

    Fragment discipline (adr-0016 §implementers): each fragment first BINDS the
    evaluated source arguments once at de Bruijn 0 (via [Ret]/[Ret (VPair ..)]), then
    is pure variable plumbing — NO val shifting exists anywhere in this file.  Each
    fragment reproduces [handle_store]'s decision order exactly; in particular
    [OSetDeadline] validates the deadline argument's SHAPE before consulting the
    store (a bad shape is [Dstuck] even on an absent key), and the is-an-int test on
    the [DSome] payload is [Prim PCmpInt [x; x]] — [DInt 0] iff [x] is an int
    (adr-0009 total prims: mismatch is [DNone]).

    Liveness in the fragments is the adr-0011 boundary, at the ELABORATED level:
    dead iff [PCmpInt [now; d] = DInt 1] (i.e. [now > d]); the [<]-liveness mutant
    (also dead at [DInt 0], i.e. at the exact deadline) is observably rejected in §9.

    Anti-vacuity (adr-0005): boundary instances at d-1 / d / d+1 through the
    elaboration (vm_compute), the mutant elaboration rejected on the boundary
    program, explicit-witness inhabitance, and [wf]-preservation with the
    all_programs vm_compute witness.  Print Assumptions must read "Closed under the
    global context" for every theorem (theories/Prims.v header note). *)

From Stdlib Require Import ZArith List String Ascii Bool Lia FMapFacts OrderedTypeEx.
From Rocqeteer Require Import EffIR Samples Journal Wf.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation length := List.length.

Module EF := FMapFacts.WFacts_fun(String_as_OT)(M).

(* ===== §1  Packing: the world projection ==================================== *)

(** The dval encoding of an optional deadline — the second component of a packed
    entry. *)
Definition pack_dl (o : option Z) : dval :=
  match o with
  | None   => DNone
  | Some d => DSome (DInt d)
  end.

(** A packed entry: value and deadline fused into ONE kernel value; the kernel
    binding itself NEVER expires ([None] — [handle_store]'s liveness test is vacuous
    on it). *)
Definition pack_entry (e : entry) : entry :=
  (DPair (fst e) (pack_dl (snd e)), None).

Definition pack_state (s : state) : state := M.map pack_entry s.

(** Store relation: the kernel store IS the packed source store, up to [M.Equal]
    (the map-observational equality — [run] reads stores only through [find]). *)
Definition kv_rel (s sk : state) : Prop := M.Equal sk (pack_state s).

(** World relation: stores packed, every other effect field EQUAL. *)
Definition wrel (w wk : world) : Prop :=
  kv_rel w.(kv) wk.(kv)
  /\ wk.(ctx)     = w.(ctx)
  /\ wk.(now_ms)  = w.(now_ms)
  /\ wk.(trace)   = w.(trace)
  /\ wk.(cache)   = w.(cache)
  /\ wk.(journal) = w.(journal).

(** Simulation of one run result: same outcome, related final worlds. *)
Definition sim (r rk : outcome * world) : Prop :=
  fst rk = fst r /\ wrel (snd r) (snd rk).

(** The canonical stuck val: [VSucc] of a non-int evaluates to [Dstuck] in every
    environment — how a fragment REPRODUCES a source [Dstuck] result. *)
Definition dstuck_val : val := VSucc VUnit.

Lemma eval_dstuck_val : forall env, eval_val env dstuck_val = Dstuck.
Proof. reflexivity. Qed.

(* ===== §2  The five fragments =============================================== *)

(** [OGet k] — kernel get, unpack, liveness at the elaborated level.
    Env layouts are annotated right of each binder ([·] = cons, leftmost = de Bruijn 0). *)
Definition elab_get (k : val) : tm :=
  Bind (Perform OGet [k])                              (* r *)
    (Match (VVar 0)
       [(PNone, Ret VNone);
        (PSome,                                        (* x·r          x = DPair v dl *)
          Match (VVar 0)
            [(PPair,                                   (* dl·v·x·r *)
              Match (VVar 0)
                [(PNone, Ret (VSome (VVar 1)));        (* no deadline: DSome v *)
                 (PSome,                               (* d·dl·v·x·r *)
                   Bind (Perform ONow [])              (* now·d·dl·v·x·r *)
                     (Bind (Prim PCmpInt [VVar 0; VVar 1])
                        (Match (VVar 0)                (* c·now·d·dl·v·x·r *)
                           [(PInt 1, Ret VNone)]      (* now > d: expired = absent *)
                           (Ret (VSome (VVar 4))))))] (* live: DSome v *)
                (Ret dstuck_val))]
            (Ret dstuck_val))]
       (Ret (VVar 0))).                                (* r = Dstuck: passthrough *)

(** [OPut k v] — pack with no deadline (put CLEARS the deadline, adr-0011). *)
Definition elab_put (k v : val) : tm :=
  Perform OPut [k; VPair v VNone].

(** [ODelete k] — the kernel removes UNCONDITIONALLY (mirrors [handle_store]:
    [M.remove] happens for every well-shaped key, lazy-expiry included); the RESULT
    is the source liveness flag, computed from the packed entry read FIRST. *)
Definition elab_delete (k : val) : tm :=
  Bind (Ret k)                                         (* kd *)
    (Bind (Perform OGet [VVar 0])                      (* r·kd *)
       (Bind (Perform ODelete [VVar 1])                (* f·r·kd   kernel flag unused *)
          (Match (VVar 1)
             [(PNone, Ret (VBool false));
              (PSome,                                  (* x·f·r·kd *)
                Match (VVar 0)
                  [(PPair,                             (* dl·v·x·f·r·kd *)
                    Match (VVar 0)
                      [(PNone, Ret (VBool true));
                       (PSome,                         (* d·dl·v·x·f·r·kd *)
                         Bind (Perform ONow [])
                           (Bind (Prim PCmpInt [VVar 0; VVar 1])
                              (Match (VVar 0)
                                 [(PInt 1, Ret (VBool false))]
                                 (Ret (VBool true)))))]
                      (Ret dstuck_val))]
                  (Ret dstuck_val))]
             (Ret (VVar 1))))).                        (* r = Dstuck: passthrough *)

(** [OGetDeadline k] — unpack; live no-deadline is [DSome DNone], live deadline is
    [DSome (DSome (DInt d))], expired/absent is [DNone] (the adr-0011 op table). *)
Definition elab_getdl (k : val) : tm :=
  Bind (Perform OGet [k])                              (* r *)
    (Match (VVar 0)
       [(PNone, Ret VNone);
        (PSome,                                        (* x·r *)
          Match (VVar 0)
            [(PPair,                                   (* dl·v·x·r *)
              Match (VVar 0)
                [(PNone, Ret (VSome VNone));
                 (PSome,                               (* d·dl·v·x·r *)
                   Bind (Perform ONow [])              (* now·d·dl·v·x·r *)
                     (Bind (Prim PCmpInt [VVar 0; VVar 1])
                        (Match (VVar 0)                (* c·now·d·dl·v·x·r *)
                           [(PInt 1, Ret VNone)]
                           (Ret (VSome (VSome (VVar 2)))))))]
                (Ret dstuck_val))]
            (Ret dstuck_val))]
       (Ret (VVar 0))).

(** [OSetDeadline k dv] — argument-shape dispatch FIRST (matching [handle_store]'s
    match order: a malformed deadline argument is [Dstuck] even when the key is
    absent), THEN kernel get + liveness + conditional repack-write.  The two write
    paths differ only in the deadline they pack ([VNone] vs the validated int
    payload), so each is spelled out concretely — parameterizing them by index
    offsets would trade auditability for de Bruijn arithmetic. *)
Definition elab_setdl (k dv : val) : tm :=
  Bind (Ret (VPair k dv))                              (* a          a = DPair kd dd *)
    (Match (VVar 0)
       [(PPair,                                        (* dd·kd·a *)
         Match (VVar 0)
           [(PNone,                                    (* dd = DNone: write path A *)
             Bind (Perform OGet [VVar 1])              (* r·dd·kd·a *)
               (Match (VVar 0)
                  [(PNone, Ret (VBool false));
                   (PSome,                             (* x·r·dd·kd·a *)
                     Match (VVar 0)
                       [(PPair,                        (* dl·v·x·r·dd·kd·a *)
                         Match (VVar 0)
                           [(PNone,                    (* live, no stored deadline *)
                             Bind (Perform OPut [VVar 5; VPair (VVar 1) VNone])
                                  (Ret (VBool true)));
                            (PSome,                    (* d·dl·v·x·r·dd·kd·a *)
                              Bind (Perform ONow [])   (* now·d·… *)
                                (Bind (Prim PCmpInt [VVar 0; VVar 1])
                                   (Match (VVar 0)    (* c·now·d·dl·v·x·r·dd·kd·a *)
                                      [(PInt 1, Ret (VBool false))]
                                      (Bind (Perform OPut
                                               [VVar 8; VPair (VVar 4) VNone])
                                            (Ret (VBool true))))))]
                           (Ret dstuck_val))]
                       (Ret dstuck_val))]
                  (Ret (VVar 0))));                    (* r = Dstuck: passthrough *)
            (PSome,                                    (* dp·dd·kd·a   dp = payload *)
              Bind (Prim PCmpInt [VVar 0; VVar 0])     (* DInt 0 iff dp is an int *)
                (Match (VVar 0)                        (* c·dp·dd·kd·a *)
                   [(PInt 0,                           (* dd = DSome (DInt _): path B *)
                     Bind (Perform OGet [VVar 3])      (* r·c·dp·dd·kd·a *)
                       (Match (VVar 0)
                          [(PNone, Ret (VBool false));
                           (PSome,                     (* x·r·c·dp·dd·kd·a *)
                             Match (VVar 0)
                               [(PPair,                (* dl·v·x·r·c·dp·dd·kd·a *)
                                 Match (VVar 0)
                                   [(PNone,
                                     Bind (Perform OPut
                                             [VVar 7; VPair (VVar 1) (VSome (VVar 5))])
                                          (Ret (VBool true)));
                                    (PSome,            (* d·dl·v·x·r·c·dp·dd·kd·a *)
                                      Bind (Perform ONow [])
                                        (Bind (Prim PCmpInt [VVar 0; VVar 1])
                                           (Match (VVar 0)
                                                     (* c2·now·d·dl·v·x·r·c·dp·dd·kd·a *)
                                              [(PInt 1, Ret (VBool false))]
                                              (Bind (Perform OPut
                                                       [VVar 10;
                                                        VPair (VVar 4) (VSome (VVar 8))])
                                                    (Ret (VBool true))))))]
                                   (Ret dstuck_val))]
                               (Ret dstuck_val))]
                          (Ret (VVar 0))))]            (* r = Dstuck: passthrough *)
                   (Ret dstuck_val)))]                 (* DSome of a non-int: Dstuck *)
           (Ret dstuck_val))]                          (* dd not DNone/DSome: Dstuck *)
       (Ret dstuck_val)).                              (* unreachable: VPair is DPair *)

(* ===== §3  The elaboration ================================================== *)

(** One [Perform] site: expiry-surface ops of the RIGHT arity get their fragment;
    every other op — including store ops at a wrong arity, whose [handle_store]
    fallthrough is [Dstuck] on both sides — passes through unchanged. *)
Definition elab_perform (o : op) (args : list val) : tm :=
  match o, args with
  | OGet,         [k]     => elab_get k
  | OPut,         [k; v]  => elab_put k v
  | ODelete,      [k]     => elab_delete k
  | OGetDeadline, [k]     => elab_getdl k
  | OSetDeadline, [k; dv] => elab_setdl k dv
  | _, _                  => Perform o args
  end.

(** The elaboration: homomorphic on every construct, [elab_perform] at ops.  The
    branch-list recursion is the [eval_val]/[run] nested-fix guardedness technique. *)
Fixpoint elab (t : tm) : tm :=
  match t with
  | Ret v          => Ret v
  | Bind t1 t2     => Bind (elab t1) (elab t2)
  | Perform o args => elab_perform o args
  | Match scrut branches default =>
      Match scrut
        ((fix eb (bs : list (pat * tm)) : list (pat * tm) :=
            match bs with
            | []                => []
            | (p, body) :: rest => (p, elab body) :: eb rest
            end) branches)
        (elab default)
  | Repeat n body  => Repeat n (elab body)
  | Prim p args    => Prim p args
  | Fold lst init body => Fold lst (elab init) (elab body)
  end.

(** Named twin of the branch map + its definitional equation (the Journal.v/Wf.v
    technique). *)
Definition elab_branches :=
  fix eb (bs : list (pat * tm)) : list (pat * tm) :=
    match bs with
    | []                => []
    | (p, body) :: rest => (p, elab body) :: eb rest
    end.

Lemma elab_match_eq : forall scrut branches default,
  elab (Match scrut branches default)
  = Match scrut (elab_branches branches) (elab default).
Proof. reflexivity. Qed.

(** Mode K's program list: the elaborated twin of the single-source list — SAME
    names, elaborated bodies; the codegen emits it into a separate generated module
    and the differential tests run it against KERNEL realizers only (adr-0016 §4). *)
Definition elab_programs : list (string * tm) :=
  map (fun nt => (fst nt, elab (snd nt))) all_programs.

(* ===== §4  Store lemmas: packing through find/add/remove ==================== *)

Lemma find_pack_state : forall k s,
  M.find k (pack_state s) = option_map pack_entry (M.find k s).
Proof. intros; apply EF.map_o. Qed.

Lemma kv_rel_find : forall s sk k, kv_rel s sk ->
  M.find k sk = option_map pack_entry (M.find k s).
Proof. intros s sk k H. rewrite (H k). apply find_pack_state. Qed.

Lemma kv_rel_add : forall s sk k e, kv_rel s sk ->
  kv_rel (M.add k e s) (M.add k (pack_entry e) sk).
Proof.
  intros s sk k e H y.
  rewrite EF.add_o, find_pack_state, EF.add_o.
  destruct (EF.eq_dec k y).
  - reflexivity.
  - apply (kv_rel_find _ _ _ H).
Qed.

Lemma kv_rel_remove : forall s sk k, kv_rel s sk ->
  kv_rel (M.remove k s) (M.remove k sk).
Proof.
  intros s sk k H y.
  rewrite EF.remove_o, find_pack_state, EF.remove_o.
  destruct (EF.eq_dec k y).
  - reflexivity.
  - apply (kv_rel_find _ _ _ H).
Qed.

Lemma kv_rel_empty : kv_rel (M.empty entry) (M.empty entry).
Proof. intro y. rewrite EF.empty_o, find_pack_state, EF.empty_o. reflexivity. Qed.

(** Rebuilding a world with its own store is the identity — the shape [handle_store]
    fallthroughs produce. *)
Lemma set_kv_kv : forall w, set_kv w w.(kv) = w.
Proof. destruct w; reflexivity. Qed.

(* ===== §5  Fragment simulation lemmas ======================================= *)

(** Each fragment lemma: for related worlds, the fragment's run equals the source
    op's run on the outcome and preserves the relation.  Proof pattern: destruct
    both worlds (so record rebuilds compute), substitute the equal fields, rewrite
    the ONE kernel [find] through [kv_rel_find], then case on the source entry and
    the liveness comparison — the fragment computes by [cbn] on each shape. *)

Lemma elab_get_sim : forall k env w wk, wrel w wk ->
  sim (run env (Perform OGet [k]) w) (run env (elab_get k) wk).
Proof.
  intros k env w wk H.
  destruct H as (Hkv & Hctx & Hnow & Htr & Hca & Hjo).
  destruct w as [s c n tr ca j]; destruct wk as [sk ck nk trk cak jk].
  cbn in Hkv, Hctx, Hnow, Htr, Hca, Hjo; subst ck nk trk cak jk.
  unfold elab_get. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  (* DBytes: the one shape [handle_store] accepts *)
  unfold find_live.
  rewrite (kv_rel_find _ _ (string_of_list_ascii kb) Hkv).
  destruct (M.find (string_of_list_ascii kb) s) as [[v dl] |] eqn:Ef; cbn.
  - (* bound: liveness by stored deadline *)
    destruct dl as [d |]; cbn.
    + (* stored deadline d: the boundary comparison *)
      unfold apply_cmp_int, Z.leb.
      destruct (Z.compare n d) eqn:Hc; cbn;
        split; [reflexivity | repeat split; assumption |
                reflexivity | repeat split; assumption |
                reflexivity | repeat split; assumption].
    + (* no stored deadline: always live *)
      split; [reflexivity | repeat split; assumption].
  - (* unbound *)
    split; [reflexivity | repeat split; assumption].
Qed.

Lemma elab_put_sim : forall k v env w wk, wrel w wk ->
  sim (run env (Perform OPut [k; v]) w) (run env (elab_put k v) wk).
Proof.
  intros k v env w wk H.
  destruct H as (Hkv & Hctx & Hnow & Htr & Hca & Hjo).
  destruct w as [s c n tr ca j]; destruct wk as [sk ck nk trk cak jk].
  cbn in Hkv, Hctx, Hnow, Htr, Hca, Hjo; subst ck nk trk cak jk.
  unfold elab_put. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  (* DBytes: the add packs *)
  split; [reflexivity |].
  repeat split; try reflexivity.
  exact (kv_rel_add _ _ _ (eval_val env v, None) Hkv).
Qed.

Lemma elab_delete_sim : forall k env w wk, wrel w wk ->
  sim (run env (Perform ODelete [k]) w) (run env (elab_delete k) wk).
Proof.
  intros k env w wk H.
  destruct H as (Hkv & Hctx & Hnow & Htr & Hca & Hjo).
  destruct w as [s c n tr ca j]; destruct wk as [sk ck nk trk cak jk].
  cbn in Hkv, Hctx, Hnow, Htr, Hca, Hjo; subst ck nk trk cak jk.
  unfold elab_delete. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  (* DBytes *)
  unfold find_live.
  rewrite (kv_rel_find _ _ (string_of_list_ascii kb) Hkv).
  destruct (M.find (string_of_list_ascii kb) s) as [[v dl] |] eqn:Ef; cbn.
  - destruct dl as [d |]; cbn.
    + unfold apply_cmp_int, Z.leb.
      destruct (Z.compare n d) eqn:Hc; cbn;
        split; [reflexivity | repeat split; try reflexivity;
                              exact (kv_rel_remove _ _ _ Hkv) |
                reflexivity | repeat split; try reflexivity;
                              exact (kv_rel_remove _ _ _ Hkv) |
                reflexivity | repeat split; try reflexivity;
                              exact (kv_rel_remove _ _ _ Hkv)].
    + split; [reflexivity | repeat split; try reflexivity;
                            exact (kv_rel_remove _ _ _ Hkv)].
  - split; [reflexivity | repeat split; try reflexivity;
                          exact (kv_rel_remove _ _ _ Hkv)].
Qed.

Lemma elab_getdl_sim : forall k env w wk, wrel w wk ->
  sim (run env (Perform OGetDeadline [k]) w) (run env (elab_getdl k) wk).
Proof.
  intros k env w wk H.
  destruct H as (Hkv & Hctx & Hnow & Htr & Hca & Hjo).
  destruct w as [s c n tr ca j]; destruct wk as [sk ck nk trk cak jk].
  cbn in Hkv, Hctx, Hnow, Htr, Hca, Hjo; subst ck nk trk cak jk.
  unfold elab_getdl. cbn.
  destruct (eval_val env k) as [| b | z | | dv | d1 d2 | kb | tg tv | ds |] eqn:Ek;
    cbn;
    try (split; [reflexivity | repeat split; assumption]).
  unfold find_live.
  rewrite (kv_rel_find _ _ (string_of_list_ascii kb) Hkv).
  destruct (M.find (string_of_list_ascii kb) s) as [[v dl] |] eqn:Ef; cbn.
  - destruct dl as [d |]; cbn.
    + unfold apply_cmp_int, Z.leb.
      destruct (Z.compare n d) eqn:Hc; cbn;
        split; [reflexivity | repeat split; assumption |
                reflexivity | repeat split; assumption |
                reflexivity | repeat split; assumption].
    + split; [reflexivity | repeat split; assumption].
  - split; [reflexivity | repeat split; assumption].
Qed.

Lemma elab_setdl_sim : forall k dv env w wk, wrel w wk ->
  sim (run env (Perform OSetDeadline [k; dv]) w) (run env (elab_setdl k dv) wk).
Proof.
  intros k dv env w wk H.
  destruct H as (Hkv & Hctx & Hnow & Htr & Hca & Hjo).
  destruct w as [s c n tr ca j]; destruct wk as [sk ck nk trk cak jk].
  cbn in Hkv, Hctx, Hnow, Htr, Hca, Hjo; subst ck nk trk cak jk.
  unfold elab_setdl. cbn.
  (* dispatch on the deadline argument's SHAPE first, like handle_store *)
  destruct (eval_val env dv) as [| b2 | z2 | | dp | e1 e2 | bs2 | tg2 tv2 | ds2 |]
    eqn:Edv; cbn;
    (* shapes handle_store rejects for EVERY key: both sides Dstuck, no state change *)
    try (destruct (eval_val env k) as [| b | z | | dvk | d1 d2 | kb | tg tv | ds |]
           eqn:Ek; cbn;
         (split; [reflexivity | repeat split; assumption])).
  - (* dd = DNone: write path A *)
    destruct (eval_val env k) as [| b | z | | dvk | d1 d2 | kb | tg tv | ds |] eqn:Ek;
      cbn;
      try (split; [reflexivity | repeat split; assumption]).
    unfold find_live.
    rewrite (kv_rel_find _ _ (string_of_list_ascii kb) Hkv).
    destruct (M.find (string_of_list_ascii kb) s) as [[v dl] |] eqn:Ef; cbn.
    + destruct dl as [d |]; cbn.
      * unfold apply_cmp_int, Z.leb.
        destruct (Z.compare n d) eqn:Hc; cbn;
          split; [reflexivity | repeat split; try reflexivity;
                                exact (kv_rel_add _ _ _ (v, None) Hkv) |
                  reflexivity | repeat split; try reflexivity;
                                exact (kv_rel_add _ _ _ (v, None) Hkv) |
                  reflexivity | repeat split; assumption].
      * split; [reflexivity | repeat split; try reflexivity;
                              exact (kv_rel_add _ _ _ (v, None) Hkv)].
    + split; [reflexivity | repeat split; assumption].
  - (* dd = DSome dp: the payload must be an int (the PCmpInt self-test) *)
    destruct dp as [| b3 | d' | | dp' | f1 f2 | bs3 | tg3 tv3 | ds3 |]; cbn;
      (* non-int payloads: Dstuck on both sides for EVERY key *)
      try (destruct (eval_val env k) as [| b | z | | dvk | d1 d2 | kb | tg tv | ds |]
             eqn:Ek; cbn;
           (split; [reflexivity | repeat split; assumption])).
    (* dp = DInt d': the is-an-int self-compare is Eq, so the gate passes *)
    unfold apply_cmp_int; rewrite Z.compare_refl; cbn.
    destruct (eval_val env k) as [| b | z | | dvk | d1 d2 | kb | tg tv | ds |] eqn:Ek;
      cbn;
      try (split; [reflexivity | repeat split; assumption]).
    unfold find_live.
    rewrite (kv_rel_find _ _ (string_of_list_ascii kb) Hkv).
    destruct (M.find (string_of_list_ascii kb) s) as [[v dl] |] eqn:Ef; cbn.
    + destruct dl as [d |]; cbn.
      * unfold apply_cmp_int, Z.leb.
        destruct (Z.compare n d) eqn:Hc; cbn;
          split; [reflexivity | repeat split; try reflexivity;
                                exact (kv_rel_add _ _ _ (v, Some d') Hkv) |
                  reflexivity | repeat split; try reflexivity;
                                exact (kv_rel_add _ _ _ (v, Some d') Hkv) |
                  reflexivity | repeat split; assumption].
      * split; [reflexivity | repeat split; try reflexivity;
                              exact (kv_rel_add _ _ _ (v, Some d') Hkv)].
    + split; [reflexivity | repeat split; assumption].
Qed.

(* ===== §6  The Perform dispatch and the construct twins ===================== *)

(** Pass-through [Perform] cases: ops that never touch the store, and store ops at a
    WRONG arity (both sides are the [handle_store] fallthrough — [Dstuck], store
    untouched).  After destructing both worlds and substituting the equal fields,
    the two runs are syntactically identical up to the store variables, which such
    an op never reads. *)
Local Ltac elab_pass H w wk :=
  destruct H as (Hkv & Hc & Hn & Ht & Hh & Hj);
  destruct w; destruct wk;
  cbn in Hkv, Hc, Hn, Ht, Hh, Hj; subst;
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
  (split; [reflexivity | repeat split; assumption]).

Lemma elab_perform_sim : forall o args env w wk, wrel w wk ->
  sim (run env (Perform o args) w) (run env (elab_perform o args) wk).
Proof.
  intros o args env w wk H.
  destruct o.
  - (* OGet *)
    destruct args as [| k [| a2 args']];
      [ elab_pass H w wk | apply elab_get_sim; exact H | elab_pass H w wk ].
  - (* OPut *)
    destruct args as [| k [| v [| a3 args']]];
      [ elab_pass H w wk | elab_pass H w wk
      | apply elab_put_sim; exact H | elab_pass H w wk ].
  - (* ODelete *)
    destruct args as [| k [| a2 args']];
      [ elab_pass H w wk | apply elab_delete_sim; exact H | elab_pass H w wk ].
  - (* OGetDeadline *)
    destruct args as [| k [| a2 args']];
      [ elab_pass H w wk | apply elab_getdl_sim; exact H | elab_pass H w wk ].
  - (* OSetDeadline *)
    destruct args as [| k [| dv [| a3 args']]];
      [ elab_pass H w wk | elab_pass H w wk
      | apply elab_setdl_sim; exact H | elab_pass H w wk ].
  - (* ONow *)      elab_pass H w wk.
  - (* OThrow *)    elab_pass H w wk.
  - (* OAsk *)      elab_pass H w wk.
  - (* OTrace *)    elab_pass H w wk.
  - (* OCacheGet *) elab_pass H w wk.
  - (* OCachePut *) elab_pass H w wk.
  - (* OJournal *)  elab_pass H w wk.
Qed.

(** Branch dispatch: environments are EQUAL on the two sides (only worlds differ),
    so the same branch fires with the same payloads; bodies are related by the
    [Forall] hypothesis. *)
Lemma try_branches_sim :
  forall branches env d default w wk,
    Forall (fun pb => forall env' w' wk', wrel w' wk' ->
              sim (run env' (snd pb) w') (run env' (elab (snd pb)) wk')) branches ->
    (forall env' w' wk', wrel w' wk' ->
        sim (run env' default w') (run env' (elab default) wk')) ->
    wrel w wk ->
    sim (try_branches env d default w branches)
        (try_branches env d (elab default) wk (elab_branches branches)).
Proof.
  induction branches as [| [p body] rest IH]; intros env d default w wk HF Hdef H.
  - cbn. apply Hdef; exact H.
  - inversion HF as [| ? ? Hbody HFrest]; subst.
    cbn. destruct (match_pat p d) as [payloads |].
    + apply Hbody; exact H.
    + apply IH; assumption.
Qed.

(** Bounded loops: same fuel, related worlds each iteration. *)
Lemma repeat_loop_sim :
  forall env body,
    (forall env' w' wk', wrel w' wk' ->
        sim (run env' body w') (run env' (elab body) wk')) ->
    forall n w wk, wrel w wk ->
      sim (repeat_loop env body n w) (repeat_loop env (elab body) n wk).
Proof.
  intros env body Hb; induction n as [| m IH]; intros w wk H; cbn.
  - split; [reflexivity | exact H].
  - pose proof (Hb env w wk H) as Hstep.
    destruct (run env body w) as [[x | e] w1];
      destruct (run env (elab body) wk) as [[xk | ek] wk1];
      destruct Hstep as [Hfst Hw]; cbn in Hfst, Hw; try discriminate.
    + apply IH; exact Hw.
    + injection Hfst as ->. split; [reflexivity | exact Hw].
Qed.

(** Fold iterations: outcomes are equal, so the two sides thread the SAME
    accumulator; worlds stay related. *)
Lemma fold_elems_sim :
  forall env body,
    (forall env' w' wk', wrel w' wk' ->
        sim (run env' body w') (run env' (elab body) wk')) ->
    forall vs acc w wk, wrel w wk ->
      sim (fold_elems env body vs acc w) (fold_elems env (elab body) vs acc wk).
Proof.
  intros env body Hb; induction vs as [| x xs IH]; intros acc w wk H.
  - cbn. split; [reflexivity | exact H].
  - rewrite !fold_elems_cons.
    pose proof (Hb (push_env [x; acc] env) w wk H) as Hstep.
    destruct (run (push_env [x; acc] env) body w) as [[acc' | e] w1];
      destruct (run (push_env [x; acc] env) (elab body) wk) as [[acck | ek] wk1];
      destruct Hstep as [Hfst Hw]; cbn in Hfst, Hw; try discriminate.
    + injection Hfst as ->. apply IH; exact Hw.
    + injection Hfst as ->. split; [reflexivity | exact Hw].
Qed.

(* ===== §7  THE TOWER THEOREM (adr-0016 §3) ================================== *)

(** For EVERY program, environment, and pair of pack-related worlds: the elaborated
    program computes the SAME outcome over the kernel fragment as the source over
    the expiring store, and the final worlds are pack-related again.  No wf side
    condition — malformed-argument [Dstuck]s are reproduced exactly.  This is the
    discharge theorem for the Expiry surface: the deadline semantics trusted in the
    fused realizer is PROVEN at the elaborated level. *)
Theorem elab_simulates : forall t env w wk, wrel w wk ->
  sim (run env t w) (run env (elab t) wk).
Proof.
  apply (tm_ind_strong (fun t => forall env w wk, wrel w wk ->
           sim (run env t w) (run env (elab t) wk))).
  - (* Ret *) intros v env w wk H; cbn. split; [reflexivity | exact H].
  - (* Bind *)
    intros t1 t2 IH1 IH2 env w wk H; cbn.
    pose proof (IH1 env w wk H) as Hstep.
    destruct (run env t1 w) as [[x | e] w1];
      destruct (run env (elab t1) wk) as [[xk | ek] wk1];
      destruct Hstep as [Hfst Hw]; cbn in Hfst, Hw; try discriminate.
    + injection Hfst as ->. apply IH2; exact Hw.
    + injection Hfst as ->. split; [reflexivity | exact Hw].
  - (* Perform *) intros o args env w wk H. apply elab_perform_sim; exact H.
  - (* Match *)
    intros scrut branches default HF Hdef env w wk H.
    rewrite elab_match_eq, !run_match_eq.
    apply try_branches_sim; assumption.
  - (* Repeat *)
    intros n body IHb env w wk H.
    cbn [elab]. rewrite !run_repeat_eq.
    apply repeat_loop_sim; assumption.
  - (* Prim *) intros p args env w wk H; cbn. split; [reflexivity | exact H].
  - (* Fold *)
    intros lst init body IHi IHb env w wk H.
    cbn [elab]. rewrite !run_fold_eq.
    pose proof (IHi env w wk H) as Hstep.
    destruct (run env init w) as [[acc0 | e] w1];
      destruct (run env (elab init) wk) as [[acck | ek] wk1];
      destruct Hstep as [Hfst Hw]; cbn in Hfst, Hw; try discriminate.
    + injection Hfst as ->.
      destruct (eval_val env lst); try (split; [reflexivity | exact Hw]).
      apply fold_elems_sim; assumption.
    + injection Hfst as ->. split; [reflexivity | exact Hw].
Qed.

(* ===== §8  Corollaries: closed form, observe-level reading ================== *)

(** Empty stores are pack-related, so every closed program is covered. *)
Corollary elab_run_top : forall t c now,
  sim (run_top c now t) (run [] (elab t) (init_world c now)).
Proof.
  intros t c now. apply elab_simulates.
  repeat split; reflexivity.
Qed.

(** From ANY seeded source store (the [observe_full] shape the differential tests
    use): pack the seed on the kernel side. *)
Corollary elab_seeded : forall t c now s,
  sim (run [] t        (mkWorld s              c now [] (M.empty dval) []))
      (run [] (elab t) (mkWorld (pack_state s) c now [] (M.empty dval) [])).
Proof.
  intros. apply elab_simulates.
  repeat split; reflexivity.
Qed.

(** The observe-level reading: outcome, trace, and journal are EQUAL; the final
    stores agree pointwise through packing ([find] is the store's observation —
    [observe]'s [elements] listing is derived from it). *)
Corollary elab_observe : forall t c now s k,
  let r  := run [] t        (mkWorld s              c now [] (M.empty dval) []) in
  let rk := run [] (elab t) (mkWorld (pack_state s) c now [] (M.empty dval) []) in
  fst rk = fst r
  /\ (snd rk).(trace)   = (snd r).(trace)
  /\ (snd rk).(journal) = (snd r).(journal)
  /\ M.find k (snd rk).(kv) = option_map pack_entry (M.find k (snd r).(kv)).
Proof.
  intros t c now s k.
  destruct (elab_seeded t c now s) as [Hfst (Hkv & _ & _ & Htr & _ & Hjo)].
  repeat split.
  - exact Hfst.
  - exact Htr.
  - exact Hjo.
  - exact (kv_rel_find _ _ k Hkv).
Qed.

(* ===== §9  wf preservation (the codegen gate accepts elaborated programs) === *)

Lemma wf_elab_get : forall depth k,
  wf_val depth k = true -> wf_tm depth (elab_get k) = true.
Proof. intros depth k H; cbn; rewrite H; reflexivity. Qed.

Lemma wf_elab_put : forall depth k v,
  wf_val depth k = true -> wf_val depth v = true ->
  wf_tm depth (elab_put k v) = true.
Proof. intros depth k v Hk Hv; cbn; rewrite Hk, Hv; reflexivity. Qed.

Lemma wf_elab_delete : forall depth k,
  wf_val depth k = true -> wf_tm depth (elab_delete k) = true.
Proof. intros depth k H; cbn; rewrite H; reflexivity. Qed.

Lemma wf_elab_getdl : forall depth k,
  wf_val depth k = true -> wf_tm depth (elab_getdl k) = true.
Proof. intros depth k H; cbn; rewrite H; reflexivity. Qed.

Lemma wf_elab_setdl : forall depth k dv,
  wf_val depth k = true -> wf_val depth dv = true ->
  wf_tm depth (elab_setdl k dv) = true.
Proof. intros depth k dv Hk Hv; cbn; rewrite Hk, Hv; reflexivity. Qed.

Lemma wf_elab_perform : forall depth o args,
  Nat.eqb (length args) (op_arity o) && forallb (wf_val depth) args = true ->
  wf_tm depth (elab_perform o args) = true.
Proof.
  intros depth o args H.
  destruct o; cbn in H;
    destruct args as [| a1 [| a2 [| a3 rest]]]; try discriminate; cbn in H;
    repeat match goal with
           | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
           end;
    cbn; try rewrite ?H, ?H0, ?H1; try reflexivity;
    auto using wf_elab_get, wf_elab_put, wf_elab_delete, wf_elab_getdl,
               wf_elab_setdl.
Qed.

(** Named twin for the wf of elaborated branch lists. *)
Lemma wf_elab_branches : forall branches depth,
  Forall (fun pb => forall depth',
            wf_tm depth' (snd pb) = true -> wf_tm depth' (elab (snd pb)) = true)
         branches ->
  wf_branches depth branches = true ->
  wf_branches depth (elab_branches branches) = true.
Proof.
  induction branches as [| [p body] rest IH]; intros depth HF Hwb; cbn in *.
  - reflexivity.
  - inversion HF as [| ? ? Hbody HFrest]; subst; cbn [snd] in Hbody.
    apply andb_true_iff in Hwb as [Hb Hr].
    rewrite (Hbody _ Hb). apply IH; assumption.
Qed.

(** The codegen wf gate (adr-0014) needs no special case for mode K: elaboration
    preserves well-formedness at every depth. *)
Theorem wf_elab : forall t depth,
  wf_tm depth t = true -> wf_tm depth (elab t) = true.
Proof.
  apply (tm_ind_strong (fun t => forall depth,
           wf_tm depth t = true -> wf_tm depth (elab t) = true)).
  - (* Ret *) intros v depth H; exact H.
  - (* Bind *)
    intros t1 t2 IH1 IH2 depth H; cbn in H |- *.
    apply andb_true_iff in H as [H1 H2].
    rewrite (IH1 _ H1), (IH2 _ H2). reflexivity.
  - (* Perform *) intros o args depth H. apply wf_elab_perform. exact H.
  - (* Match *)
    intros scrut branches default HF Hdef depth H.
    rewrite wf_tm_match_eq in H.
    apply andb_true_iff in H as [H1 Hwd];
      apply andb_true_iff in H1 as [Hs Hwb].
    rewrite elab_match_eq, wf_tm_match_eq.
    rewrite Hs, (wf_elab_branches _ _ HF Hwb), (Hdef _ Hwd). reflexivity.
  - (* Repeat *) intros n body IHb depth H; cbn in H |- *. apply IHb; exact H.
  - (* Prim *) intros p args depth H; exact H.
  - (* Fold *)
    intros lst init body IHi IHb depth H; cbn in H |- *.
    apply andb_true_iff in H as [H1 Hb]; apply andb_true_iff in H1 as [Hl Hi].
    rewrite Hl, (IHi _ Hi), (IHb _ Hb). reflexivity.
Qed.

(* ===== §10  Anti-vacuity (adr-0005) ========================================= *)

(** Boundary probe: put, set deadline [d], get — one closed program end-to-end. *)
Definition probe_key : list ascii := list_ascii_of_string "x".

Definition probe (d : Z) : tm :=
  Bind (Perform OPut [VBytes probe_key; VInt 42])
    (Bind (Perform OSetDeadline [VBytes probe_key; VSome (VInt d)])
       (Perform OGet [VBytes probe_key])).

(** d-1 / d / d+1 at [now = 100], source AND elaborated: alive AT the deadline,
    dead 1ms after — the adr-0011 boundary reproduced at the elaborated level. *)
Theorem elab_boundary_expired :
  fst (run [] (elab (probe 99)) (init_world DUnit 100)) = ORet DNone
  /\ fst (run_top DUnit 100 (probe 99)) = ORet DNone.
Proof. split; vm_compute; reflexivity. Qed.

Theorem elab_boundary_at_deadline :
  fst (run [] (elab (probe 100)) (init_world DUnit 100)) = ORet (DSome (DInt 42))
  /\ fst (run_top DUnit 100 (probe 100)) = ORet (DSome (DInt 42)).
Proof. split; vm_compute; reflexivity. Qed.

Theorem elab_boundary_live :
  fst (run [] (elab (probe 101)) (init_world DUnit 100)) = ORet (DSome (DInt 42))
  /\ fst (run_top DUnit 100 (probe 101)) = ORet (DSome (DInt 42)).
Proof. split; vm_compute; reflexivity. Qed.

(** MUTANT ELABORATION (the adr-0005 proof-mutation companion): [<]-liveness in the
    get fragment — ALSO dead when [PCmpInt [now; d] = DInt 0], i.e. at the exact
    deadline.  A full local twin of [elab]; EffIR untouched (the TimeStore.v
    local-mutant technique). *)
Definition elab_get_mutant (k : val) : tm :=
  Bind (Perform OGet [k])
    (Match (VVar 0)
       [(PNone, Ret VNone);
        (PSome,
          Match (VVar 0)
            [(PPair,
              Match (VVar 0)
                [(PNone, Ret (VSome (VVar 1)));
                 (PSome,
                   Bind (Perform ONow [])
                     (Bind (Prim PCmpInt [VVar 0; VVar 1])
                        (Match (VVar 0)
                           [(PInt 1, Ret VNone);
                            (PInt 0, Ret VNone)]        (* MUTANT: dead AT d too *)
                           (Ret (VSome (VVar 4))))))]
                (Ret dstuck_val))]
            (Ret dstuck_val))]
       (Ret (VVar 0))).

Definition elab_perform_mutant (o : op) (args : list val) : tm :=
  match o, args with
  | OGet, [k] => elab_get_mutant k
  | _, _      => elab_perform o args
  end.

Fixpoint elab_mutant (t : tm) : tm :=
  match t with
  | Ret v          => Ret v
  | Bind t1 t2     => Bind (elab_mutant t1) (elab_mutant t2)
  | Perform o args => elab_perform_mutant o args
  | Match scrut branches default =>
      Match scrut
        ((fix eb (bs : list (pat * tm)) : list (pat * tm) :=
            match bs with
            | []                => []
            | (p, body) :: rest => (p, elab_mutant body) :: eb rest
            end) branches)
        (elab_mutant default)
  | Repeat n body  => Repeat n (elab_mutant body)
  | Prim p args    => Prim p args
  | Fold lst init body => Fold lst (elab_mutant init) (elab_mutant body)
  end.

(** The mutant is observably WRONG exactly at the boundary — [elab_simulates] is
    FALSE with [elab_mutant] in place of [elab] (this instance refutes it)... *)
Theorem elab_mutant_rejected :
  fst (run [] (elab_mutant (probe 100)) (init_world DUnit 100))
  <> fst (run_top DUnit 100 (probe 100)).
Proof. vm_compute. intro H; discriminate H. Qed.

(** ... while agreeing away from the boundary: the mutation is PLAUSIBLE — the
    boundary kills it, not a broken fragment. *)
Theorem elab_mutant_plausible :
  fst (run [] (elab_mutant (probe 101)) (init_world DUnit 100))
  = fst (run_top DUnit 100 (probe 101)).
Proof. vm_compute. reflexivity. Qed.

(** Explicit-witness inhabitance: a deadline-carrying related world pair exists,
    and the elaborated get REALLY reads through the packing on it. *)
Definition probe_seeded : state :=
  M.add (string_of_list_ascii probe_key) (DInt 7, Some 100) (M.empty entry).

Theorem elab_precondition_inhabited :
  wrel (mkWorld probe_seeded DUnit 100 [] (M.empty dval) [])
       (mkWorld (pack_state probe_seeded) DUnit 100 [] (M.empty dval) [])
  /\ fst (run [] (elab (Perform OGet [VBytes probe_key]))
              (mkWorld (pack_state probe_seeded) DUnit 100 [] (M.empty dval) []))
     = ORet (DSome (DInt 7)).
Proof.
  split.
  - repeat split; reflexivity.
  - vm_compute. reflexivity.
Qed.

(** The elaborated single-source list is wf — the codegen wf gate accepts every
    mode-K program (the vm_compute inhabitance companion of [wf_elab]). *)
Theorem elab_all_programs_wf :
  forallb (fun nt => wf_tm 0%nat (snd nt)) elab_programs = true.
Proof. vm_compute. reflexivity. Qed.

(* ===== §11  Print Assumptions =============================================== *)

(** Each must read "Closed under the global context". *)
Print Assumptions elab_simulates.
Print Assumptions elab_run_top.
Print Assumptions elab_seeded.
Print Assumptions elab_observe.
Print Assumptions wf_elab.
Print Assumptions elab_boundary_expired.
Print Assumptions elab_boundary_at_deadline.
Print Assumptions elab_boundary_live.
Print Assumptions elab_mutant_rejected.
Print Assumptions elab_mutant_plausible.
Print Assumptions elab_precondition_inhabited.
Print Assumptions elab_all_programs_wf.
