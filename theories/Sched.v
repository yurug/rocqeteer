(** * Sched — C5 cooperative scheduler on the CEK machine (adr-0019 §Decision 1/6).

    The concurrency layer, built on the ADEQUATE step machine (theories/Cek.v).
    Fibers SHARE one [world]; each fiber is a world-free CEK frame state ([fstate]).
    A fiber runs via [Cek.step] (world threaded out) until it HALTS or reaches a
    concurrency op — a scheduling point — then the SCHEDULER acts on the op.  The
    five ops are NOT reduced by the machine (they are sequentially [Dstuck], EffIR):
    the scheduler intercepts them, so channels/fibers/schedule live HERE, not in the
    world.

    DETERMINISM BY INJECTION (adr-0019 §Decision 1): the interleaving is the injected
    [schedule : list fiber_id].  [run_sched] is a FUNCTION of it — a fixed schedule
    yields a deterministic transcript; the only nondeterminism source is the
    schedule (the C4 connection-script oracle generalized to interleaving order).

    SAFETY BY CONSTRUCTION: fibers share ONLY through channels — there is no
    shared-memory op — so DATA RACES ARE NOT REPRESENTABLE (structural, not proven).
    Deadlock (all fibers blocked on empty channels) is a modeled STUCK result, never
    a hang.

    Anti-vacuity (this file, axiom-free vm_compute): [schedule_matters] (one program,
    two schedules, DIFFERENT transcripts — the oracle genuinely controls
    interleaving); [seq_embedding] (a single concurrency-free fiber = its sequential
    [run]); [deadlock] (mutual empty-recv reaches Stuck); [producer_consumer]
    (OChanSend/OChanRecv across fibers); [spawn_runs] (OSpawn adds a fiber).  The
    GENERAL sequential-embedding theorem (run_sched under the singleton schedule =
    big-step run, via [Cek.cek_adequate]) and the concurrent HTTP driver are the next
    unit; the OCaml Effect.Deep scheduler is gated on its own review (adr-0019). *)

From Stdlib Require Import List ZArith.
From Rocqeteer Require Import EffIR Cek.
Import ListNotations.
Local Open Scope Z_scope.

(* ===== §1  Z-keyed association helpers ====================================== *)

Fixpoint lookupZ {A} (k : Z) (l : list (Z * A)) : option A :=
  match l with
  | []            => None
  | (k', v) :: l' => if Z.eqb k' k then Some v else lookupZ k l'
  end.

Fixpoint updateZ {A} (k : Z) (v : A) (l : list (Z * A)) : list (Z * A) :=
  match l with
  | []            => [(k, v)]
  | (k', v') :: l' => if Z.eqb k' k then (k', v) :: l' else (k', v') :: updateZ k v l'
  end.

Fixpoint removeZ {A} (k : Z) (l : list (Z * A)) : list (Z * A) :=
  match l with
  | []            => []
  | (k', v') :: l' => if Z.eqb k' k then l' else (k', v') :: removeZ k l'
  end.

Definition enqueue (c : Z) (v : dval) (chans : list (Z * list dval))
  : list (Z * list dval) :=
  match lookupZ c chans with
  | Some q => updateZ c (q ++ [v]) chans
  | None   => chans
  end.

Definition dequeue (c : Z) (chans : list (Z * list dval))
  : option (dval * list (Z * list dval)) :=
  match lookupZ c chans with
  | Some (v :: q) => Some (v, updateZ c q chans)
  | _             => None
  end.

(* ===== §2  Fibers: world-free CEK frame states ============================== *)

(** A fiber is a CEK config minus the (shared) world. *)
Inductive fstate : Type :=
| FE : tm -> list dval -> kont -> fstate
| FR : outcome -> kont -> fstate.

Definition to_cfg (f : fstate) (w : world) : config :=
  match f with FE t e k => CEval t e k w | FR o k => CRet o k w end.

Definition of_cfg (c : config) : fstate * world :=
  match c with CEval t e k w => (FE t e k, w) | CRet o k w => (FR o k, w) end.

(** One machine step against the SHARED world (reuses [Cek.step]). *)
Definition fstep (f : fstate) (w : world) : fstate * world :=
  of_cfg (step (to_cfg f w)).

Definition is_conc (o : op) : bool :=
  match o with
  | OSpawn | OYield | OChanMake | OChanSend | OChanRecv => true
  | _ => false
  end.

(** A fiber is at a scheduling point when focused on a concurrency op. *)
Definition fconc (f : fstate) : option (op * list val * list dval * kont) :=
  match f with
  | FE (Perform o args) env k => if is_conc o then Some (o, args, env, k) else None
  | _ => None
  end.

Definition fdone (f : fstate) : bool :=
  match f with FR _ [] => true | _ => false end.

(** Run a fiber to its next scheduling point (halt or a concurrency op), threading
    the shared world.  Fuel-bounded (cooperative: scheduling points are finite). *)
Fixpoint run_to_sched (fuel : nat) (f : fstate) (w : world) : fstate * world :=
  match fuel with
  | O    => (f, w)
  | S m  =>
      if fdone f then (f, w)
      else match fconc f with
           | Some _ => (f, w)
           | None   => let '(f', w') := fstep f w in run_to_sched m f' w'
           end
  end.

(* ===== §3  The scheduler state and one scheduling step ====================== *)

Record sst : Type := mkS {
  swld   : world;
  sfib   : list (Z * fstate);        (* live fibers by id *)
  schan  : list (Z * list dval);     (* channel FIFO queues *)
  sdone  : list (Z * outcome);       (* completed fibers, in completion order *)
  snextf : Z;                        (* next fiber id (OSpawn) *)
  snextc : Z;                        (* next channel id (OChanMake) *)
}.

Definition RTS_FUEL : nat := 1000%nat.

(** Run one scheduled fiber to its next scheduling point, then act on the op.
    [bodies] maps a spawn index to its statically-named fiber body (adr-0019 Q1). *)
Definition sched_one (bodies : Z -> tm) (fid : Z) (s : sst) : sst :=
  match lookupZ fid s.(sfib) with
  | None => s                        (* already completed / unknown: no-op *)
  | Some f =>
      let '(f', w') := run_to_sched RTS_FUEL f s.(swld) in
      if fdone f' then
        match f' with
        | FR o _ => mkS w' (removeZ fid s.(sfib)) s.(schan)
                        (s.(sdone) ++ [(fid, o)]) s.(snextf) s.(snextc)
        | _      => s
        end
      else
        match fconc f' with
        | Some (OYield, _, _, k) =>
            mkS w' (updateZ fid (FR (ORet DUnit) k) s.(sfib))
                s.(schan) s.(sdone) s.(snextf) s.(snextc)
        | Some (OChanMake, _, _, k) =>
            let c := s.(snextc) in
            mkS w' (updateZ fid (FR (ORet (DInt c)) k) s.(sfib))
                (s.(schan) ++ [(c, [])]) s.(sdone) s.(snextf) (c + 1)
        | Some (OChanSend, args, env, k) =>
            match map (eval_val env) args with
            | [DInt c; v] =>
                mkS w' (updateZ fid (FR (ORet DUnit) k) s.(sfib))
                    (enqueue c v s.(schan)) s.(sdone) s.(snextf) s.(snextc)
            | _ =>
                mkS w' (updateZ fid (FR (ORet Dstuck) k) s.(sfib))
                    s.(schan) s.(sdone) s.(snextf) s.(snextc)
            end
        | Some (OChanRecv, args, env, k) =>
            match map (eval_val env) args with
            | [DInt c] =>
                match dequeue c s.(schan) with
                | Some (v, ch') =>
                    mkS w' (updateZ fid (FR (ORet v) k) s.(sfib))
                        ch' s.(sdone) s.(snextf) s.(snextc)
                | None =>          (* empty: fiber BLOCKS — no progress this slot *)
                    mkS w' s.(sfib) s.(schan) s.(sdone) s.(snextf) s.(snextc)
                end
            | _ =>
                mkS w' (updateZ fid (FR (ORet Dstuck) k) s.(sfib))
                    s.(schan) s.(sdone) s.(snextf) s.(snextc)
            end
        | Some (OSpawn, args, env, k) =>
            match map (eval_val env) args with
            | [DInt bidx] =>
                let nf := s.(snextf) in
                mkS w'
                  ((updateZ fid (FR (ORet (DInt nf)) k) s.(sfib))
                     ++ [(nf, FE (bodies bidx) [] [])])
                  s.(schan) s.(sdone) (nf + 1) s.(snextc)
            | _ =>
                mkS w' (updateZ fid (FR (ORet Dstuck) k) s.(sfib))
                    s.(schan) s.(sdone) s.(snextf) s.(snextc)
            end
        | _ =>                       (* fuel out (never with enough): keep world *)
            mkS w' s.(sfib) s.(schan) s.(sdone) s.(snextf) s.(snextc)
        end
  end.

(** Drive the whole injected schedule — a FUNCTION of it (determinism by injection). *)
Fixpoint run_sched (bodies : Z -> tm) (sch : list Z) (s : sst) : sst :=
  match sch with
  | []          => s
  | fid :: rest => run_sched bodies rest (sched_one bodies fid s)
  end.

Inductive sresult : Type :=
| Completed : list (Z * outcome) -> sresult
| Stuck     : list Z -> list (Z * outcome) -> sresult.   (* remaining fibers + done *)

Definition sresult_of (s : sst) : sresult :=
  match s.(sfib) with
  | [] => Completed s.(sdone)
  | _  => Stuck (map fst s.(sfib)) s.(sdone)
  end.

Definition init_sst (w0 : world) (fs : list (Z * fstate))
    (chs : list (Z * list dval)) (nf nc : Z) : sst :=
  mkS w0 fs chs [] nf nc.

(* ===== §4  Structural facts ================================================= *)

Lemma run_sched_nil : forall bodies s, run_sched bodies [] s = s.
Proof. reflexivity. Qed.

Lemma sched_one_absent : forall bodies fid s,
  lookupZ fid s.(sfib) = None -> sched_one bodies fid s = s.
Proof. intros bodies fid s H. unfold sched_one. rewrite H. reflexivity. Qed.

(* ===== §5  Anti-vacuity — the scheduler really schedules ==================== *)

Definition nb : Z -> tm := fun _ => Ret VUnit.        (* no spawn bodies *)
Definition w0 : world := init_world DUnit 0.

(** Interleaving: fiber A traces 10, YIELDS, traces 11; fiber B traces 20.  The
    schedule controls where B interleaves — [1;2;1] vs [1;1;2] give DIFFERENT
    traces, and both complete. *)
Definition fA : tm :=
  Bind (Perform OTrace [VInt 10])
    (Bind (Perform OYield []) (Perform OTrace [VInt 11])).
Definition fB : tm := Perform OTrace [VInt 20].
Definition s_int : sst := init_sst w0 [(1, FE fA [] []); (2, FE fB [] [])] [] 3 1.

Theorem schedule_matters :
  trace (swld (run_sched nb [1; 2; 1] s_int))
  <> trace (swld (run_sched nb [1; 1; 2] s_int)).
Proof. vm_compute. intro H; discriminate H. Qed.

Theorem interleavings_complete :
  sfib (run_sched nb [1; 2; 1] s_int) = []
  /\ sfib (run_sched nb [1; 1; 2] s_int) = [].
Proof. split; vm_compute; reflexivity. Qed.

(** The [1;2;1] interleaving is exactly [10; 20; 11] (B lands between A's halves). *)
Theorem interleaving_121 :
  rev (trace (swld (run_sched nb [1; 2; 1] s_int)))
  = [DInt 10; DInt 20; DInt 11].
Proof. vm_compute. reflexivity. Qed.

(** A single concurrency-free fiber runs to exactly its SEQUENTIAL [run] — same
    trace, same outcome recorded.  (The general theorem — every conc-free fiber, any
    long-enough singleton schedule — is the next unit, via [Cek.cek_adequate].) *)
Definition fS : tm := Bind (Perform OTrace [VInt 10]) (Perform OTrace [VInt 11]).
Definition s_seq : sst := init_sst w0 [(1, FE fS [] [])] [] 2 1.

Theorem seq_embedding :
  trace (swld (run_sched nb [1] s_seq)) = trace (snd (run [] fS w0))
  /\ sdone (run_sched nb [1] s_seq) = [(1, fst (run [] fS w0))].
Proof. split; vm_compute; reflexivity. Qed.

(** Deadlock: two fibers each recv on a distinct EMPTY channel, no senders.  Every
    schedule leaves both blocked — a modeled Stuck result, not a hang. *)
Definition fD1 : tm := Perform OChanRecv [VInt 0].
Definition fD2 : tm := Perform OChanRecv [VInt 1].
Definition s_dead : sst :=
  init_sst w0 [(1, FE fD1 [] []); (2, FE fD2 [] [])] [(0, []); (1, [])] 3 2.

Theorem deadlock :
  sresult_of (run_sched nb [1; 2; 1; 2] s_dead) = Stuck [1; 2] [].
Proof. vm_compute. reflexivity. Qed.

(** Producer/consumer across fibers: send 42 on channel 0, recv it, trace it.
    Exercises OChanSend + OChanRecv (with block-then-progress on [1;2;2]). *)
Definition fProd : tm := Perform OChanSend [VInt 0; VInt 42].
Definition fCons : tm :=
  Bind (Perform OChanRecv [VInt 0]) (Perform OTrace [VVar 0]).
Definition s_pc : sst :=
  init_sst w0 [(1, FE fProd [] []); (2, FE fCons [] [])] [(0, [])] 3 1.

Theorem producer_consumer :
  rev (trace (swld (run_sched nb [1; 2; 2; 1] s_pc))) = [DInt 42]
  /\ sfib (run_sched nb [1; 2; 2; 1] s_pc) = [].
Proof. split; vm_compute; reflexivity. Qed.

(** Even when the consumer runs FIRST (recv on empty → block), a later slot makes
    progress — same result, different schedule. *)
Theorem producer_consumer_blocked_first :
  rev (trace (swld (run_sched nb [2; 1; 2; 2; 1] s_pc))) = [DInt 42].
Proof. vm_compute. reflexivity. Qed.

(** OSpawn: a fiber spawns body 0 (which traces 99); the spawned fiber runs. *)
Definition bodies_sp : Z -> tm :=
  fun i => if Z.eqb i 0 then Perform OTrace [VInt 99] else Ret VUnit.
Definition fSp : tm := Perform OSpawn [VInt 0].
Definition s_sp : sst := init_sst w0 [(1, FE fSp [] [])] [] 2 1.

Theorem spawn_runs :
  In (DInt 99) (trace (swld (run_sched bodies_sp [1; 2; 1] s_sp)))
  /\ sfib (run_sched bodies_sp [1; 2; 1] s_sp) = [].
Proof. split; vm_compute; try reflexivity; auto. Qed.

(* ===== §5b  The GENERAL single-fiber sequential embedding =================== *)

(** The scheduler bookkeeping is proven GENERAL: for ANY term whose fiber runs (to a
    halted state) with exactly big-step [run]'s result — hypothesis [Hrun], the clean
    interface to the machine — a single-fiber schedule [[fid]] reaps it into the done
    list with [run]'s outcome, and leaves the shared world at [run]'s final world and
    no fibers remaining.  [Hrun] is dischargeable: [Cek.cek_drive_run] gives, for
    EVERY term, a fuel driving the CEK machine to exactly [run]; for a concurrency-free
    term that fuel makes [run_to_sched] (which never stops at a conc op) equal
    [run] — witnessed concretely just below and, in general, via the conc-free
    invariant (the next unit).  This isolates the schedule/transcript accounting as
    the proven-general part. *)
Theorem seq_embedding_general : forall t w1 fid nf nc,
  run_to_sched RTS_FUEL (FE t [] []) w1
  = (FR (fst (run [] t w1)) [], snd (run [] t w1)) ->
  let s := run_sched nb [fid] (init_sst w1 [(fid, FE t [] [])] [] nf nc) in
  swld s = snd (run [] t w1)
  /\ sdone s = [(fid, fst (run [] t w1))]
  /\ sfib s = [].
Proof.
  intros t w1 fid nf nc Hrun. cbn zeta.
  assert (Hlk : lookupZ fid [(fid, FE t [] [])] = Some (FE t [] []))
    by (simpl; rewrite Z.eqb_refl; reflexivity).
  assert (Hrm : removeZ fid [(fid, FE t [] [])] = [])
    by (simpl; rewrite Z.eqb_refl; reflexivity).
  unfold run_sched, sched_one, init_sst; cbn [sfib swld schan sdone snextf snextc].
  rewrite Hlk; cbn [fst snd].
  rewrite Hrun; cbn [fdone].
  rewrite Hrm.
  repeat split; reflexivity.
Qed.

(** [Hrun] is inhabited: the concurrency-free [fS] discharges it by [vm_compute], so
    the general theorem specializes to the concrete sequential embedding — the same
    fact [seq_embedding] states, now as an instance of the general accounting. *)
Theorem fS_runs_to_run :
  run_to_sched RTS_FUEL (FE fS [] []) w0
  = (FR (fst (run [] fS w0)) [], snd (run [] fS w0)).
Proof. vm_compute. reflexivity. Qed.

Corollary seq_embedding_fS :
  swld (run_sched nb [1] (init_sst w0 [(1, FE fS [] [])] [] 2 1))
    = snd (run [] fS w0)
  /\ sdone (run_sched nb [1] (init_sst w0 [(1, FE fS [] [])] [] 2 1))
    = [(1, fst (run [] fS w0))].
Proof.
  destruct (seq_embedding_general fS w0 1 2 1 fS_runs_to_run) as (Hw & Hd & _).
  split; [exact Hw | exact Hd].
Qed.

(* ===== §5c  The conc-free invariant: Hrun discharged by law, not by vm ====== *)

(** A term is CONCURRENCY-FREE when no reachable [Perform] targets a concurrency op.
    Branch bodies recurse through an inline nested fix (the standard single-Fixpoint
    encoding of list-of-subterms recursion — a genuine mutual fixpoint is rejected by
    the guard on the hidden [snd]/component projection). *)
Fixpoint conc_free (t : tm) : Prop :=
  match t with
  | Ret _          => True
  | Bind a b       => conc_free a /\ conc_free b
  | Perform o _    => is_conc o = false
  | Match _ bs d   =>
      (fix cfb (l : list (pat * tm)) : Prop :=
         match l with
         | []          => True
         | (_, b) :: r => conc_free b /\ cfb r
         end) bs
      /\ conc_free d
  | Repeat _ b     => conc_free b
  | Prim _ _       => True
  | Fold _ i b     => conc_free i /\ conc_free b
  end.

(** Standalone branch predicate (references the closed [conc_free] constant) and the
    bridge to the inline form above. *)
Fixpoint conc_free_branches (bs : list (pat * tm)) : Prop :=
  match bs with
  | []          => True
  | (_, b) :: r => conc_free b /\ conc_free_branches r
  end.

Lemma conc_free_Match : forall s bs d,
  conc_free (Match s bs d) <-> conc_free_branches bs /\ conc_free d.
Proof.
  intros s bs d; cbn [conc_free]; split.
  - intros [Hb Hd]; split; [| exact Hd]; revert Hb.
    induction bs as [| [p b] r IH]; cbn; intros Hb; [exact I |].
    destruct Hb as [h t0]; split; [exact h | exact (IH t0)].
  - intros [Hb Hd]; split; [| exact Hd]; revert Hb.
    induction bs as [| [p b] r IH]; cbn; intros Hb; [exact I |].
    destruct Hb as [h t0]; split; [exact h | exact (IH t0)].
Qed.

(** Extended to machine states: the focused term AND every term buried in the
    continuation frames must be conc-free (a pending [KB]/[KRep]/[KFold] body becomes
    the focus after a return, so the invariant must reach into the stack). *)
Definition conc_free_frame (fr : frame) : Prop :=
  match fr with KB t2 _ => conc_free t2 | KRep _ b _ => conc_free b | KFold _ b _ => conc_free b end.

Definition conc_free_kont (k : kont) : Prop := Forall conc_free_frame k.

Definition conc_free_cfg (c : config) : Prop :=
  match c with
  | CEval t _ k _ => conc_free t /\ conc_free_kont k
  | CRet _ k _    => conc_free_kont k
  end.

Definition conc_free_fstate (f : fstate) : Prop :=
  match f with FE t _ k => conc_free t /\ conc_free_kont k | FR _ k => conc_free_kont k end.

(** [select] lands on a conc-free body: the chosen branch (or default) is one of the
    conc-free terms.  Induction on the branch list. *)
Lemma select_conc_free : forall d env bs default,
  conc_free_branches bs -> conc_free default ->
  conc_free (fst (select d env bs default)).
Proof.
  induction bs as [| [p b] r IH]; intros default Hb Hd; simpl in Hb |- *.
  - exact Hd.
  - destruct Hb as [Hhead Htail]; simpl in Hhead.
    destruct (match_pat p d) as [pl |] eqn:E; simpl.
    + exact Hhead.
    + apply IH; assumption.
Qed.

(** [step] preserves the invariant: every frame it pushes carries a term the source
    term already contained (so conc-freedom is inherited), and it never fabricates a
    concurrency op.  This is the heart — it makes the machine-interface hypothesis a
    theorem, not an assumption. *)
Lemma step_conc_free : forall c, conc_free_cfg c -> conc_free_cfg (step c).
Proof.
  intros c H; destruct c as [t env k w | r k w]; cbn [step].
  - destruct H as [Ht Hk];
      destruct t as [v0 | a1 a2 | o args | scr bs def | n body | p args | lst ini body].
    + (* Ret *) exact Hk.
    + (* Bind *) cbn [conc_free] in Ht; destruct Ht as [H1 H2].
      split; [exact H1 | apply Forall_cons; assumption].
    + (* Perform *) destruct (run env (Perform _ _) w) as [r w']; exact Hk.
    + (* Match *) destruct (proj1 (conc_free_Match scr bs def) Ht) as [Hbs Hd].
      destruct (select (eval_val env scr) env bs def) as [bdy env'] eqn:Es.
      pose proof (select_conc_free (eval_val env scr) env bs def Hbs Hd) as Hsel.
      rewrite Es in Hsel; cbn [fst] in Hsel. split; assumption.
    + (* Repeat *) cbn [conc_free] in Ht.
      destruct n; [exact Hk | split; [exact Ht | apply Forall_cons; assumption]].
    + (* Prim *) destruct (run env (Prim _ _) w) as [r w']; exact Hk.
    + (* Fold *) cbn [conc_free] in Ht; destruct Ht as [Hi Hb].
      split; [exact Hi | apply Forall_cons; [exact Hb | exact Hk]].
  - (* CRet: step consumes/refocuses a frame *)
    destruct k as [| fr k']; cbn [conc_free_cfg conc_free_kont] in *.
    + exact H.
    + apply Forall_inv in H as Hf; apply Forall_inv_tail in H as Hk'.
      destruct fr as [t2 e2 | m body e | xs body e]; cbn [conc_free_frame] in Hf.
      * destruct r as [x | er]; cbn [conc_free_cfg]; [split; assumption | exact Hk'].
      * destruct r as [x | er]; cbn [conc_free_cfg conc_free]; [split; assumption | exact Hk'].
      * destruct r as [x | er]; cbn [conc_free_cfg]; [| exact Hk'].
        destruct xs as [| y xs']; [exact Hk' | split; [exact Hf | apply Forall_cons; assumption]].
Qed.

(* Roundtrips between the world-free fiber state and the machine config. *)
Lemma of_cfg_to_cfg : forall f w, of_cfg (to_cfg f w) = (f, w).
Proof. intros [t e k | o k] w; reflexivity. Qed.

Lemma conc_free_of_cfg : forall c, conc_free_cfg c -> conc_free_fstate (fst (of_cfg c)).
Proof. intros [t e k w | o k w] H; exact H. Qed.

Lemma to_cfg_of_cfg : forall c, to_cfg (fst (of_cfg c)) (snd (of_cfg c)) = c.
Proof. intros [t e k w | o k w]; reflexivity. Qed.

Lemma fdone_halted : forall f w, fdone f = halted (to_cfg f w).
Proof. intros [t e k | o k] w; [reflexivity | destruct k; reflexivity]. Qed.

(** A conc-free fiber is NEVER at a scheduling point: [fconc] is [None], so
    [run_to_sched] never stops early to hand control to the scheduler. *)
Lemma fconc_conc_free : forall f, conc_free_fstate f -> fconc f = None.
Proof.
  intros [t e k | o k] H; [| reflexivity].
  destruct t; try reflexivity. cbn [conc_free_fstate conc_free] in H.
  destruct H as [Ho _]. cbn [fconc]. rewrite Ho. reflexivity.
Qed.

(** THE bridge: for a conc-free fiber, [run_to_sched] (the scheduler's per-fiber
    driver) IS [Cek.drive] — it never diverts to the scheduler, so it just iterates
    [step].  General over fuel and state. *)
Lemma run_to_sched_drive : forall n f w,
  conc_free_fstate f ->
  run_to_sched n f w = of_cfg (drive n (to_cfg f w)).
Proof.
  induction n as [| m IH]; intros f w Hcf; cbn [run_to_sched drive].
  - rewrite of_cfg_to_cfg; reflexivity.
  - rewrite (fdone_halted f w). destruct (halted (to_cfg f w)) eqn:Eh.
    + rewrite of_cfg_to_cfg; reflexivity.
    + rewrite (fconc_conc_free f Hcf). unfold fstep.
      destruct (of_cfg (step (to_cfg f w))) as [f' w'] eqn:Eo.
      rewrite (IH f' w').
      * assert (Hc : to_cfg f' w' = step (to_cfg f w)).
        { pose proof (to_cfg_of_cfg (step (to_cfg f w))) as Hto.
          rewrite Eo in Hto; cbn [fst snd] in Hto; exact Hto. }
        rewrite Hc. reflexivity.
      * pose proof (conc_free_of_cfg (step (to_cfg f w))) as Hcp.
        rewrite Eo in Hcp; cbn [fst] in Hcp.
        apply Hcp, step_conc_free; destruct f; exact Hcf.
Qed.

(** The DISCHARGE law (adr-0019): for EVERY concurrency-free program, the scheduler's
    single-fiber driver reaches exactly big-step [run] — outcome, world, halted with no
    frames — with enough fuel.  This turns [seq_embedding_general]'s [Hrun] hypothesis
    into a theorem for the whole conc-free class: sequential (file/socket) programs
    embed into the scheduler BY LAW, not by [vm_compute] on one witness.  Corollary of
    the conc-free invariant plus [Cek.cek_drive_run]. *)
Theorem conc_free_embeds : forall t w,
  conc_free t ->
  exists n, run_to_sched n (FE t [] []) w
            = (FR (fst (run [] t w)) [], snd (run [] t w)).
Proof.
  intros t w Hcf.
  destruct (cek_drive_run t [] w) as [n Hn].
  exists n. rewrite (run_to_sched_drive n (FE t [] []) w).
  - cbn [to_cfg]. rewrite Hn. reflexivity.
  - split; [exact Hcf | constructor].
Qed.

(* The scheduler's per-fiber budget is the fixed [RTS_FUEL]; the discharge above is
   existential in fuel.  To feed it into the [RTS_FUEL]-budgeted [run_sched] we need
   only that once [run_to_sched] reaches a done state, MORE fuel is stable — i.e. the
   driver parks on halted configs (via [Cek.drive]). *)
Lemma fdone_fst_of_cfg : forall c, fdone (fst (of_cfg c)) = halted c.
Proof. intros [t e k w | o k w]; [reflexivity | destruct k; reflexivity]. Qed.

Lemma drive_mono : forall n c,
  halted (drive n c) = true -> forall m, (n <= m)%nat -> drive m c = drive n c.
Proof.
  induction n as [| k IH]; intros c Hn m Hm; cbn [drive] in Hn.
  - apply drive_stable; exact Hn.
  - destruct (halted c) eqn:Hc.
    + rewrite (drive_stable m c Hc), (drive_stable (S k) c Hc); reflexivity.
    + destruct m as [| m']; [inversion Hm |].
      cbn [drive]; rewrite Hc.
      apply (IH (step c) Hn m'); apply le_S_n; exact Hm.
Qed.

Lemma run_to_sched_ge : forall n f w,
  conc_free_fstate f ->
  fdone (fst (run_to_sched n f w)) = true ->
  forall m, (n <= m)%nat -> run_to_sched m f w = run_to_sched n f w.
Proof.
  intros n f w Hcf Hdone m Hm.
  rewrite (run_to_sched_drive n f w Hcf) in Hdone.
  rewrite fdone_fst_of_cfg in Hdone.
  rewrite (run_to_sched_drive m f w Hcf), (run_to_sched_drive n f w Hcf).
  rewrite (drive_mono n (to_cfg f w) Hdone m Hm). reflexivity.
Qed.

(** The general embedding, HYPOTHESIS-FREE for conc-free programs that fit the fixed
    scheduler budget: the single-fiber [run_sched] reaps [run]'s outcome into the done
    list, leaves the shared world at [run]'s final world, no fibers remaining.  The
    only side condition is the budget — some fuel [n <= RTS_FUEL] reaches a done state
    — which every closed conc-free program satisfies concretely (and unboundedly by
    [conc_free_embeds]).  This is [seq_embedding_general] with its [Hrun] DISCHARGED by
    the conc-free invariant, not assumed. *)
Theorem seq_embedding_cf : forall t w1 fid nf nc,
  conc_free t ->
  (exists n, (n <= RTS_FUEL)%nat
             /\ fdone (fst (run_to_sched n (FE t [] []) w1)) = true) ->
  let s := run_sched nb [fid] (init_sst w1 [(fid, FE t [] [])] [] nf nc) in
  swld s = snd (run [] t w1)
  /\ sdone s = [(fid, fst (run [] t w1))]
  /\ sfib s = [].
Proof.
  intros t w1 fid nf nc Hcf [n [Hle Hdn]]. cbn zeta.
  assert (Hfs : conc_free_fstate (FE t [] [])) by (split; [exact Hcf | constructor]).
  (* At RTS_FUEL the driver has parked on the same done state as at [n]. *)
  assert (HR : run_to_sched RTS_FUEL (FE t [] []) w1
               = run_to_sched n (FE t [] []) w1)
    by (apply (run_to_sched_ge n (FE t [] []) w1 Hfs Hdn); exact Hle).
  (* And [conc_free_embeds] identifies that stable value with [run]: [n] and [ne]
     reach the SAME halted state (both done → equal at their max, hence equal). *)
  destruct (conc_free_embeds t w1 Hcf) as [ne Hne].
  assert (Hn_target : run_to_sched n (FE t [] []) w1
                      = (FR (fst (run [] t w1)) [], snd (run [] t w1))).
  { destruct (Nat.le_ge_cases n ne) as [Hnn | Hnn].
    - rewrite <- (run_to_sched_ge n (FE t [] []) w1 Hfs Hdn ne Hnn). exact Hne.
    - assert (Hdne : fdone (fst (run_to_sched ne (FE t [] []) w1)) = true)
        by (rewrite Hne; reflexivity).
      rewrite (run_to_sched_ge ne (FE t [] []) w1 Hfs Hdne n Hnn). exact Hne. }
  assert (Hcommon : run_to_sched RTS_FUEL (FE t [] []) w1
                    = (FR (fst (run [] t w1)) [], snd (run [] t w1)))
    by (rewrite HR; exact Hn_target).
  assert (Hlk : lookupZ fid [(fid, FE t [] [])] = Some (FE t [] []))
    by (simpl; rewrite Z.eqb_refl; reflexivity).
  assert (Hrm : removeZ fid [(fid, FE t [] [])] = [])
    by (simpl; rewrite Z.eqb_refl; reflexivity).
  unfold run_sched, sched_one, init_sst; cbn [sfib swld schan sdone snextf snextc].
  rewrite Hlk; cbn [fst snd]. rewrite Hcommon; cbn [fdone].
  rewrite Hrm. repeat split; reflexivity.
Qed.

(* ===== §6  Print Assumptions ================================================ *)

(** Each must read "Closed under the global context". *)
Print Assumptions schedule_matters.
Print Assumptions seq_embedding.
Print Assumptions deadlock.
Print Assumptions producer_consumer.
Print Assumptions spawn_runs.
Print Assumptions seq_embedding_general.
Print Assumptions seq_embedding_fS.
Print Assumptions conc_free_embeds.
Print Assumptions seq_embedding_cf.
