(** * Journal — R9 theorem set for the Journal effect (adr-0013-journal-effect),
    plus the PDivFloor prim boundaries (adr-0009 discipline: ADR-free addition).

    Every concrete theorem is fully proved by vm_compute on a CLOSED run; the frame law
    and the run-sequence composition lemma are proven GENERALLY (plain structural
    induction — no vm_compute needed). Print Assumptions must read "Closed under the
    global context" for each. Witnesses are EXPLICIT, never [eexists] followed by a
    multi-goal vm_compute (theories/Prims.v header note).

    Contents:
    1. ORDER law: [sample_journal] journals e1 (DBytes); e2 (DTag-structured); e3 (via a
       Fold over the context list, itself a nested DList) — the chronological journal is
       exactly [(now,e1); (now,e2); (now,e3)], timestamps = the run's single instant,
       proven at TWO different now values; [observe_full] exposes it alongside the trace.
    2. FRAME law, GENERAL ([run_journal_frame]): for EVERY term, environment, world and
       initial journal, the run's outcome and all non-journal observables are independent
       of the initial journal contents, and the final journal = new entries ++ initial
       (newest-first; chronological corollary included). The journal is write-only by
       construction — this is the adr-0013 §Decision 3 law. Proven by structural
       induction over [tm] via a strengthened induction principle ([tm_ind_strong],
       covering the Match branch list) and named twins of [run]'s nested fixes.
    3. COMPOSITION, GENERAL ([run_seq_is_fold_left]): running a LIST of programs in
       sequence (threading the world) IS a left fold of the run wrapper — pure structural
       reasoning; a concrete 2-program instance is exercised by vm_compute.
    4. Error short-circuit: [sample_journal_throw] appends k = 2 entries then throws —
       exactly those k entries survive (OErr commits prior state); a throw-first program
       journals nothing.
    5. MUTANT (anti-vacuity): a local interpreter whose OJournal READS the journal
       (returns DInt (length journal) instead of DUnit) is observably different from the
       reference AND violates the frame law on a concrete probe — the read-back coupling
       the frame law kills.
    6. PDivFloor boundaries: floor-vs-truncation on negative dividends ((-7)/2 = -4),
       division by zero -> DNone, int64_min / -1 -> DNone (range-checked), shape/arity mismatch.
    7. Inhabitance (explicit witnesses) + the Print Assumptions block. *)

From Stdlib Require Import ZArith List String Ascii.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

(* ===== §1  ORDER law ======================================================== *)

(** The three entries: e1 = bytes, e2 = tagged command, e3 = the (nested-DList) context
    element journaled from inside the Fold body. *)
Definition je1 : dval := DBytes jmsg_bytes.
Definition je2 : dval := DTag 5 (DPair (DBytes jtag_bytes) (DInt 3)).
Definition je3 : dval := DList [DInt 1; DTag 2 DUnit].
Definition jctx : dval := DList [je3].

(** Chronological journal of a run from the initial world. *)
Definition run_journal (c : dval) (now : Z) (t : tm) : list (Z * dval) :=
  rev (journal (snd (run_top c now t))).

(** Program order IS journal order, every timestamp is the run's instant — at now = 0... *)
Theorem journal_order_at_zero :
  run_journal jctx 0 sample_journal = [(0, je1); (0, je2); (0, je3)].
Proof. vm_compute. reflexivity. Qed.

(** ... and at a second, distinct instant (the timestamps follow the run's now). *)
Theorem journal_order_at_5000 :
  run_journal jctx 5000 sample_journal = [(5000, je1); (5000, je2); (5000, je3)].
Proof. vm_compute. reflexivity. Qed.

(** [observe_full] exposes the chronological journal ALONGSIDE the trace (adr-0013
    §Decision 1); [sample_journal] writes no store key and no trace event. *)
Theorem journal_in_observe_full :
  observe_full jctx 0 (M.empty entry) sample_journal
  = (ORet DUnit, [], [], [(0, je1); (0, je2); (0, je3)]).
Proof. vm_compute. reflexivity. Qed.

(* ===== §2  FRAME law (GENERAL) ============================================= *)

(** Strengthened induction principle for [tm]: the stock one gives no hypothesis for the
    Match branch bodies (they sit under [list (pat * tm)]). Same nested-fix technique as
    [run] itself, so the fixpoint is structurally guarded. The case hypotheses are plain
    fixpoint ARGUMENTS (no Section/Hypothesis vernacular — the CI axiom gate is lexical). *)
Fixpoint tm_ind_strong (P : tm -> Prop)
    (HRet     : forall v, P (Ret v))
    (HBind    : forall t1 t2, P t1 -> P t2 -> P (Bind t1 t2))
    (HPerform : forall o args, P (Perform o args))
    (HMatch   : forall scrut branches default,
        Forall (fun pb => P (snd pb)) branches -> P default ->
        P (Match scrut branches default))
    (HRepeat  : forall n body, P body -> P (Repeat n body))
    (HPrim    : forall p args, P (Prim p args))
    (HFold    : forall lst init body, P init -> P body -> P (Fold lst init body))
    (t : tm) {struct t} : P t :=
  let F := tm_ind_strong P HRet HBind HPerform HMatch HRepeat HPrim HFold in
  match t with
  | Ret v        => HRet v
  | Bind t1 t2   => HBind t1 t2 (F t1) (F t2)
  | Perform o a  => HPerform o a
  | Match s bs d =>
      HMatch s bs d
        ((fix branches_ind (l : list (pat * tm)) : Forall (fun pb => P (snd pb)) l :=
            match l with
            | []            => Forall_nil _
            | (p, b) :: l'  => Forall_cons (p, b) (F b) (branches_ind l')
            end) bs)
        (F d)
  | Repeat n b   => HRepeat n b (F b)
  | Prim p a     => HPrim p a
  | Fold l i b   => HFold l i b (F i) (F b)
  end.

(** Journal plumbing facts — all definitional except the record eta. *)
Lemma journal_set_journal : forall w l, journal (set_journal w l) = l.
Proof. reflexivity. Qed.

Lemma set_journal_twice : forall w a b, set_journal (set_journal w a) b = set_journal w b.
Proof. reflexivity. Qed.

Lemma world_eta_journal : forall w, set_journal w (journal w) = w.
Proof. destruct w; reflexivity. Qed.

(** [jframe f]: f only APPENDS to the journal and never reads it — running from initial
    journal [j] equals running from the empty journal, with [j] re-attached underneath
    the new entries; everything else (outcome included) is journal-independent. *)
Definition jframe (f : world -> outcome * world) : Prop :=
  forall w j,
    f (set_journal w j)
    = (fst (f (set_journal w [])),
       set_journal (snd (f (set_journal w [])))
                   (journal (snd (f (set_journal w []))) ++ j)).

(** Unfolded form at an arbitrary starting world (its own journal plays the role of j). *)
Lemma jframe_unfold :
  forall (f : world -> outcome * world),
    jframe f ->
    forall w j,
      f (set_journal w (journal w ++ j))
      = (fst (f w), set_journal (snd (f w)) (journal (snd (f w)) ++ j)).
Proof.
  intros f Hf w j.
  pose proof (Hf w (journal w)) as B; rewrite world_eta_journal in B.
  rewrite B; cbn [fst snd].
  rewrite journal_set_journal, set_journal_twice, <- app_assoc.
  apply Hf.
Qed.

Lemma jframe_ext :
  forall f g, (forall w, f w = g w) -> jframe g -> jframe f.
Proof. intros f g E Hg w j. rewrite !E. apply Hg. Qed.

(** The workhorse: sequencing preserves the frame property (the Bind/Repeat/Fold shape). *)
Lemma jframe_bind :
  forall (f : world -> outcome * world) (g : dval -> world -> outcome * world),
    jframe f -> (forall x, jframe (g x)) ->
    jframe (fun w => match f w with
                     | (ORet x, w') => g x w'
                     | (OErr e, w') => (OErr e, w')
                     end).
Proof.
  intros f g Hf Hg w j.
  rewrite Hf.
  destruct (f (set_journal w [])) as [o w']; cbn [fst snd].
  destruct o as [x | e].
  - apply (jframe_unfold (g x) (Hg x)).
  - reflexivity.
Qed.

(** Named twins of [run]'s anonymous nested fixes, connected to [run] by definitional
    equations (proved by [reflexivity]) so the induction can speak about them. *)
Definition repeat_loop (env : list dval) (body : tm) :=
  fix loop (m : nat) (w0 : world) {struct m} : outcome * world :=
    match m with
    | O    => (ORet DUnit, w0)
    | S m' => match run env body w0 with
              | (ORet _, w1) => loop m' w1
              | (OErr e, w1) => (OErr e, w1)
              end
    end.

Lemma run_repeat_eq : forall env n body w,
  run env (Repeat n body) w = repeat_loop env body n w.
Proof. reflexivity. Qed.

Definition fold_elems (env : list dval) (body : tm) :=
  fix fe (xs : list dval) (acc : dval) (w0 : world) {struct xs} : outcome * world :=
    match xs with
    | []       => (ORet acc, w0)
    | x :: xs' => match run (push_env [x; acc] env) body w0 with
                  | (ORet acc', w1) => fe xs' acc' w1
                  | (OErr e, w1)    => (OErr e, w1)
                  end
    end.

Lemma run_fold_eq : forall env lst init body w,
  run env (Fold lst init body) w
  = match run env init w with
    | (OErr e, w')    => (OErr e, w')
    | (ORet acc0, w') =>
        match eval_val env lst with
        | DList vs => fold_elems env body vs acc0 w'
        | _        => (ORet acc0, w')
        end
    end.
Proof.
  intros. cbn.
  destruct (run env init w) as [[x | e] w']; [destruct (eval_val env lst)|]; reflexivity.
Qed.

Definition try_branches (env : list dval) (d : dval) (default : tm) (w : world) :=
  fix tb (bs : list (pat * tm)) : outcome * world :=
    match bs with
    | []                => run env default w
    | (p, body) :: rest =>
        match match_pat p d with
        | Some payloads => run (push_env payloads env) body w
        | None          => tb rest
        end
    end.

Lemma run_match_eq : forall env scrut branches default w,
  run env (Match scrut branches default) w
  = try_branches env (eval_val env scrut) default w branches.
Proof. reflexivity. Qed.

Lemma repeat_loop_frame :
  forall env body,
    jframe (run env body) ->
    forall n, jframe (repeat_loop env body n).
Proof.
  intros env body Hb n; induction n as [| m IHm].
  - intros w j; reflexivity.
  - apply jframe_ext with
      (g := fun w => match run env body w with
                     | (ORet x, w1) => repeat_loop env body m w1
                     | (OErr e, w1) => (OErr e, w1)
                     end).
    + intro w; reflexivity.
    + apply jframe_bind; [exact Hb | intro x; exact IHm].
Qed.

Lemma fold_elems_frame :
  forall env body,
    (forall env', jframe (run env' body)) ->
    forall xs acc, jframe (fun w => fold_elems env body xs acc w).
Proof.
  intros env body Hb xs; induction xs as [| x xs' IH]; intro acc.
  - intros w j; reflexivity.
  - apply jframe_ext with
      (g := fun w => match run (push_env [x; acc] env) body w with
                     | (ORet acc', w1) => fold_elems env body xs' acc' w1
                     | (OErr e, w1)    => (OErr e, w1)
                     end).
    + intro w; reflexivity.
    + apply jframe_bind; [apply Hb | intro acc'; apply IH].
Qed.

Lemma try_branches_frame :
  forall env d default,
    (forall env', jframe (run env' default)) ->
    forall bs, Forall (fun pb => forall env', jframe (run env' (snd pb))) bs ->
    jframe (fun w => try_branches env d default w bs).
Proof.
  intros env d default Hd bs HF; induction HF as [| [p body] rest Hpb _ IH].
  - intros w j; cbn. apply Hd.
  - intros w j; cbn.
    destruct (match_pat p d) as [payloads |].
    + apply (Hpb (push_env payloads env)).
    + apply (IH w j).
Qed.

(** THE FRAME LAW (adr-0013 §Decision 3, stated generally): for every term, environment,
    world and initial journal, the run appends the SAME new entries and produces the SAME
    outcome and non-journal state as the run from an empty journal — the initial journal
    is only re-attached underneath. The journal is write-only.

    [handle_store] is kept opaque during THIS proof only, so the store ops stay one
    destructible call instead of cbn-exploding into liveness case analysis (the store
    never touches the journal — that is all the proof needs). *)
Opaque handle_store handle_file.
Theorem run_journal_frame : forall t env, jframe (run env t).
Proof.
  apply (tm_ind_strong (fun t => forall env, jframe (run env t))).
  - (* Ret *) intros v env w j; reflexivity.
  - (* Bind *)
    intros t1 t2 IH1 IH2 env.
    apply jframe_ext with
      (g := fun w => match run env t1 w with
                     | (ORet x, w') => run (x :: env) t2 w'
                     | (OErr e, w') => (OErr e, w')
                     end).
    + intro w; reflexivity.
    + apply jframe_bind; [apply IH1 | intro x; apply IH2].
  - (* Perform *)
    intros o args env w j; destruct o; cbn;
      repeat match goal with
             | |- context [handle_store ?a ?b ?c ?d] =>
                 destruct (handle_store a b c d) as [? ?]
             | |- context [handle_file ?a ?b ?c ?d ?e] =>
                 destruct (handle_file a b c d e) as [? [[? ?] ?]]
             end;
      try reflexivity;
      destruct (map (eval_val env) args) as [| va vsa];
      try destruct va; try destruct vsa as [| vb vsb];
      try destruct vsb as [| vc vsc]; reflexivity.
  - (* Match *)
    intros scrut branches default HF Hd env.
    apply jframe_ext with
      (g := fun w => try_branches env (eval_val env scrut) default w branches).
    + intro w; apply run_match_eq.
    + apply try_branches_frame; [apply Hd |].
      eapply Forall_impl; [| exact HF]. cbn. intros pb Hpb env'. apply Hpb.
  - (* Repeat *)
    intros n body Hb env.
    apply jframe_ext with (g := repeat_loop env body n).
    + intro w; apply run_repeat_eq.
    + apply repeat_loop_frame, Hb.
  - (* Prim *) intros p args env w j; reflexivity.
  - (* Fold *)
    intros lst init body Hi Hb env.
    apply jframe_ext with
      (g := fun w => match run env init w with
                     | (OErr e, w')    => (OErr e, w')
                     | (ORet acc0, w') =>
                         match eval_val env lst with
                         | DList vs => fold_elems env body vs acc0 w'
                         | _        => (ORet acc0, w')
                         end
                     end).
    + intro w; apply run_fold_eq.
    + apply jframe_bind; [apply Hi |].
      intro acc0. destruct (eval_val env lst);
        try (intros w j; reflexivity).
      apply fold_elems_frame, Hb.
Qed.
Transparent handle_store handle_file.

(** Corollary, the adr-0013 reading: the OUTCOME is independent of the prior journal. *)
Corollary journal_frame_outcome :
  forall t env w j1 j2,
    fst (run env t (set_journal w j1)) = fst (run env t (set_journal w j2)).
Proof.
  intros t env w j1 j2.
  rewrite (run_journal_frame t env w j1), (run_journal_frame t env w j2); reflexivity.
Qed.

(** Corollary: every non-journal observable of the final world is independent too. *)
Corollary journal_frame_observables :
  forall t env w j,
    let w1 := snd (run env t (set_journal w j)) in
    let w0 := snd (run env t (set_journal w [])) in
    kv w1 = kv w0 /\ trace w1 = trace w0 /\ cache w1 = cache w0
    /\ ctx w1 = ctx w0 /\ now_ms w1 = now_ms w0.
Proof.
  intros t env w j; rewrite (run_journal_frame t env w j); cbn.
  repeat split; reflexivity.
Qed.

(** Corollary, chronological form: final journal = initial ++ new entries. *)
Corollary journal_frame_chronological :
  forall t env w j,
    rev (journal (snd (run env t (set_journal w j))))
    = rev j ++ rev (journal (snd (run env t (set_journal w [])))).
Proof.
  intros t env w j; rewrite (run_journal_frame t env w j); cbn.
  rewrite rev_app_distr; reflexivity.
Qed.

(** Concrete vm_compute instance: [sample_journal] run from a world seeded with a prior
    entry — same outcome, and the chronological journal is prior ++ the three new ones. *)
Definition jseed : list (Z * dval) := [(-7, DInt 0)].
Definition seeded_world : world :=
  mkWorld (M.empty entry) jctx 0 [] (M.empty dval) jseed (M.empty (list ascii)) [] 3.

Theorem journal_frame_concrete_journal :
  rev (journal (snd (run [] sample_journal seeded_world)))
  = rev jseed ++ [(0, je1); (0, je2); (0, je3)].
Proof. vm_compute. reflexivity. Qed.

Theorem journal_frame_concrete_outcome :
  fst (run [] sample_journal seeded_world)
  = fst (run_top jctx 0 sample_journal).
Proof. vm_compute. reflexivity. Qed.

(* ===== §3  COMPOSITION: run-sequence is a left fold ========================= *)

(** The sequencing wrapper consumers replay with: run one closed program, keep the
    world (state + journal threading made explicit by the recursion). *)
Definition run_step (w : world) (p : tm) : world := snd (run [] p w).

Fixpoint run_seq (ps : list tm) (w : world) : world :=
  match ps with
  | []       => w
  | p :: ps' => run_seq ps' (run_step w p)
  end.

(** THE GENERIC LEMMA (adr-0013 §Decision 3): sequential execution over a LIST of
    programs IS a left fold of the run wrapper. Pure structural reasoning. *)
Theorem run_seq_is_fold_left :
  forall ps w, run_seq ps w = fold_left run_step ps w.
Proof. induction ps as [| p ps' IH]; intros w; cbn; [reflexivity | apply IH]. Qed.

(** The 2-program reading: p1;p2 (threading the world) is the 2-fold of run. *)
Theorem run_seq_two :
  forall p1 p2 w, run_seq [p1; p2] w = run_step (run_step w p1) p2.
Proof. reflexivity. Qed.

(** Concrete 2-program instance, exercised by vm_compute: [sample_journal] then
    [sample_journal_throw] — the journals CONCATENATE in program order (three entries
    from the first run, then the two pre-throw counter entries from the second). *)
Theorem run_seq_concrete :
  rev (journal (run_seq [sample_journal; sample_journal_throw] (init_world jctx 0)))
  = [(0, je1); (0, je2); (0, je3); (0, DSome (DInt 1)); (0, DSome (DInt 2))].
Proof. vm_compute. reflexivity. Qed.

Theorem run_seq_concrete_is_fold :
  run_seq [sample_journal; sample_journal_throw] (init_world jctx 0)
  = fold_left run_step [sample_journal; sample_journal_throw] (init_world jctx 0).
Proof. vm_compute. reflexivity. Qed.

(* ===== §4  Error short-circuit ============================================= *)

(** [sample_journal_throw] appends k = 2 entries (the Repeat-read counter values, in
    order), then throws: exactly those k entries survive, the post-throw append never
    runs, and the pre-throw store writes commit (OErr state-commit discipline). *)
Theorem journal_error_short_circuit :
  observe_full DUnit 0 (M.empty entry) sample_journal_throw
  = (OErr (DBytes jboom_bytes),
     [("0"%string, (DInt 2, None))],
     [],
     [(0, DSome (DInt 1)); (0, DSome (DInt 2))]).
Proof. vm_compute. reflexivity. Qed.

(** k = 0: a throw BEFORE any append leaves the journal empty. *)
Definition journal_throw_first : tm :=
  Bind (Perform OThrow [VInt 1]) (Perform OJournal [VInt 2]).

Theorem journal_error_zero_entries :
  observe_full DUnit 0 (M.empty entry) journal_throw_first
  = (OErr (DInt 1), [], [], []).
Proof. vm_compute. reflexivity. Qed.

(* ===== §5  MUTANT: an OJournal that READS the journal ====================== *)

(** The mutant interpreter — verbatim [run], except OJournal RETURNS
    DInt (length journal) (a read-back) instead of DUnit. Defined locally, EffIR
    untouched — the TimeStore.v / Fold.v mutant technique. *)
Fixpoint run_jread (env : list dval) (t : tm) (w : world) : outcome * world :=
  match t with
  | Ret v        => (ORet (eval_val env v), w)
  | Bind t1 t2   =>
      match run_jread env t1 w with
      | (ORet x, w') => run_jread (x :: env) t2 w'
      | (OErr e, w') => (OErr e, w')
      end
  | Perform o args =>
      let vs := map (eval_val env) args in
      match o with
      | OThrow => (OErr (nth 0 vs Dstuck), w)
      | OAsk   => (ORet w.(ctx), w)
      | ONow   => (ORet (DInt w.(now_ms)), w)
      | OTrace => match vs with
                  | [v] => (ORet DUnit, set_trace w (v :: w.(trace)))
                  | _   => (ORet Dstuck, w)
                  end
      | OCacheGet => match vs with
                     | [DBytes kb] =>
                         (ORet (opt_to_dval (M.find (string_of_list_ascii kb) w.(cache))), w)
                     | _        => (ORet Dstuck, w)
                     end
      | OCachePut => match vs with
                     | [DBytes kb; v] =>
                         (ORet DUnit, set_cache w (M.add (string_of_list_ascii kb) v w.(cache)))
                     | _           => (ORet Dstuck, w)
                     end
      | OJournal => match vs with
                    | [v] => (* MUTANT: the append RESULT reads the journal length *)
                        (ORet (DInt (Z.of_nat (List.length w.(journal)))),
                         set_journal w ((w.(now_ms), v) :: w.(journal)))
                    | _   => (ORet Dstuck, w)
                    end
      | _      => let '(r, s') := handle_store w.(now_ms) o vs w.(kv) in (ORet r, set_kv w s')
      end
  | Match scrut branches default =>
      let d := eval_val env scrut in
      (fix try_bs (bs : list (pat * tm)) {struct bs} : outcome * world :=
         match bs with
         | []           => run_jread env default w
         | (p, body) :: rest =>
             match match_pat p d with
             | Some payloads => run_jread (push_env payloads env) body w
             | None => try_bs rest
             end
         end) branches
  | Repeat n body =>
      (fix loop (m : nat) (w0 : world) {struct m} : outcome * world :=
         match m with
         | O    => (ORet DUnit, w0)
         | S m' => match run_jread env body w0 with
                   | (ORet _, w1) => loop m' w1
                   | (OErr e, w1) => (OErr e, w1)
                   end
         end) n w
  | Prim p args =>
      let vs := map (eval_val env) args in
      (ORet (apply_prim p vs), w)
  | Fold lst init body =>
      let d := eval_val env lst in
      match run_jread env init w with
      | (OErr e, w') => (OErr e, w')
      | (ORet acc0, w') =>
          match d with
          | DList vs =>
              (fix fe (xs : list dval) (acc : dval) (w0 : world) {struct xs}
                 : outcome * world :=
                 match xs with
                 | []       => (ORet acc, w0)
                 | x :: xs' =>
                     match run_jread (push_env [x; acc] env) body w0 with
                     | (ORet acc', w1) => fe xs' acc' w1
                     | (OErr e, w1)    => (OErr e, w1)
                     end
                 end) vs acc0 w'
          | _ => (ORet acc0, w')
          end
      end
  end.

(** The probe: two appends; the second one's RESULT is where a read-back leaks. *)
Definition journal_probe : tm :=
  Bind (Perform OJournal [VInt 1]) (Perform OJournal [VInt 2]).

(** The mutant is OBSERVABLY different from the reference on the probe (reference:
    ORet DUnit; mutant: ORet (DInt 1) — it saw the first entry). *)
Theorem mutant_jread_observably_differs :
  (let '(o, _) := run [] journal_probe (init_world DUnit 0) in o)
  <> (let '(o, _) := run_jread [] journal_probe (init_world DUnit 0) in o).
Proof. vm_compute. intro H. discriminate H. Qed.

(** The mutant VIOLATES the frame law: its outcome depends on the prior journal
    (empty start: DInt 1; seeded start: DInt 2)... *)
Definition seeded_probe_world : world :=
  mkWorld (M.empty entry) DUnit 0 [] (M.empty dval) jseed (M.empty (list ascii)) [] 3.

Theorem mutant_jread_violates_frame :
  (let '(o, _) := run_jread [] journal_probe (init_world DUnit 0) in o)
  <> (let '(o, _) := run_jread [] journal_probe seeded_probe_world in o).
Proof. vm_compute. intro H. discriminate H. Qed.

(** ... while the reference outcome is the same on both worlds — the concrete face of
    [journal_frame_outcome], so the frame statements genuinely reject the mutant. *)
Theorem reference_frame_on_probe :
  (let '(o, _) := run [] journal_probe (init_world DUnit 0) in o)
  = (let '(o, _) := run [] journal_probe seeded_probe_world in o).
Proof. vm_compute. reflexivity. Qed.

(* ===== §6  PDivFloor boundaries (adr-0009 discipline) ======================= *)

(** FLOOR, not truncation: the negative-dividend case is where the two DIFFER
    ((-7)/2 = -4 floor; truncation would give -3) — the realizer must use Z.fdiv. *)
Theorem div_floor_neg_dividend :
  apply_prim PDivFloor [DInt (-7); DInt 2] = DSome (DInt (-4)).
Proof. vm_compute. reflexivity. Qed.

Theorem div_floor_neg_divisor :
  apply_prim PDivFloor [DInt 7; DInt (-2)] = DSome (DInt (-4)).
Proof. vm_compute. reflexivity. Qed.

Theorem div_floor_both_neg :
  apply_prim PDivFloor [DInt (-7); DInt (-2)] = DSome (DInt 3).
Proof. vm_compute. reflexivity. Qed.

Theorem div_floor_pos :
  apply_prim PDivFloor [DInt 7; DInt 2] = DSome (DInt 3).
Proof. vm_compute. reflexivity. Qed.

(** Division by zero is DNone — total, option-encoded, no error machinery. *)
Theorem div_floor_by_zero :
  apply_prim PDivFloor [DInt 5; DInt 0] = DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem div_floor_zero_by_zero :
  apply_prim PDivFloor [DInt 0; DInt 0] = DNone.
Proof. vm_compute. reflexivity. Qed.

(** The consumer driver (TTL-style rounding): (pttl + 500) / 1000 — pttl = 999 rounds
    up to 1, pttl = 499 rounds down to 0, and a NEGATIVE pttl floors toward -infinity
    ((-501 + 500) / 1000 = -1, not 0 — the truncation trap). *)
Theorem div_floor_ttl_round_up :
  apply_prim PDivFloor [DInt (999 + 500); DInt 1000] = DSome (DInt 1).
Proof. vm_compute. reflexivity. Qed.

Theorem div_floor_ttl_round_down :
  apply_prim PDivFloor [DInt (499 + 500); DInt 1000] = DSome (DInt 0).
Proof. vm_compute. reflexivity. Qed.

Theorem div_floor_ttl_negative :
  apply_prim PDivFloor [DInt (-501 + 500); DInt 1000] = DSome (DInt (-1)).
Proof. vm_compute. reflexivity. Qed.

(** int64 boundaries: min/max by one are exact; int64_min / -1 = 2^63 is the one result
    that leaves int64 range — an exact Z on both sides (no wrapping exists anywhere). *)
Theorem div_floor_min_by_one :
  apply_prim PDivFloor [DInt int64_min; DInt 1] = DSome (DInt int64_min).
Proof. vm_compute. reflexivity. Qed.

Theorem div_floor_max_by_neg_one :
  apply_prim PDivFloor [DInt int64_max; DInt (-1)] = DSome (DInt (-int64_max)).
Proof. vm_compute. reflexivity. Qed.

(** The one int64-range escape: floor(int64_min / -1) = 2^63 is OUT of range -> DNone
    (Checked-family convention; kills the single overflow the operation admits). *)
Theorem div_floor_min_by_neg_one_overflows :
  apply_prim PDivFloor [DInt int64_min; DInt (-1)] = DNone.
Proof. vm_compute. reflexivity. Qed.

(** Shape / arity mismatch -> DNone (adr-0009 §Decision 2). *)
Theorem div_floor_mismatch_shape :
  apply_prim PDivFloor [DBytes (list_ascii_of_string "7"); DInt 2] = DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem div_floor_mismatch_arity :
  apply_prim PDivFloor [DInt 7] = DNone.
Proof. vm_compute. reflexivity. Qed.

(* ===== §7  Inhabitance ====================================================== *)

(** A context on which [sample_journal] genuinely journals the stated three entries
    exists — explicit witness (snd of the closed run), vm_compute on a closed term. *)
Lemma journal_inhabited :
  exists w,
    run_top jctx 0 sample_journal = (ORet DUnit, w)
    /\ rev (journal w) = [(0, je1); (0, je2); (0, je3)].
Proof.
  exists (snd (run_top jctx 0 sample_journal)).
  split; vm_compute; reflexivity.
Qed.

(** A world with a non-empty prior journal exists and the frame law's precondition is
    inhabited on it (its journal really is jseed). *)
Lemma seeded_world_inhabited :
  exists w, journal w = jseed /\ ctx w = jctx.
Proof.
  exists seeded_world. split; vm_compute; reflexivity.
Qed.

(** Print Assumptions footprint — each must say "Closed under the global context". *)
Print Assumptions journal_order_at_zero.
Print Assumptions journal_order_at_5000.
Print Assumptions journal_in_observe_full.
Print Assumptions run_journal_frame.
Print Assumptions journal_frame_outcome.
Print Assumptions journal_frame_observables.
Print Assumptions journal_frame_chronological.
Print Assumptions journal_frame_concrete_journal.
Print Assumptions journal_frame_concrete_outcome.
Print Assumptions run_seq_is_fold_left.
Print Assumptions run_seq_two.
Print Assumptions run_seq_concrete.
Print Assumptions run_seq_concrete_is_fold.
Print Assumptions journal_error_short_circuit.
Print Assumptions journal_error_zero_entries.
Print Assumptions mutant_jread_observably_differs.
Print Assumptions mutant_jread_violates_frame.
Print Assumptions reference_frame_on_probe.
Print Assumptions div_floor_neg_dividend.
Print Assumptions div_floor_neg_divisor.
Print Assumptions div_floor_both_neg.
Print Assumptions div_floor_pos.
Print Assumptions div_floor_by_zero.
Print Assumptions div_floor_zero_by_zero.
Print Assumptions div_floor_ttl_round_up.
Print Assumptions div_floor_ttl_round_down.
Print Assumptions div_floor_ttl_negative.
Print Assumptions div_floor_min_by_one.
Print Assumptions div_floor_max_by_neg_one.
Print Assumptions div_floor_min_by_neg_one_overflows.
Print Assumptions div_floor_mismatch_shape.
Print Assumptions div_floor_mismatch_arity.
Print Assumptions journal_inhabited.
Print Assumptions seeded_world_inhabited.
