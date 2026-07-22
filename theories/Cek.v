(** * Cek — C5.1 adequacy SPIKE (adr-0019 §Decision 3, §Risk): the fiber step machine.

    The load-bearing question for C5: interleaving needs a RESUMABLE fiber, but
    big-step [run] runs to completion and has no continuation.  The proposed answer
    (adr-0019 §Decision 2) is a **defunctionalized continuation** — a frame-stack
    STEP MACHINE over the SAME [tm] (an evaluation strategy, not a second IR).  A
    second strategy is only honest if it AGREES with the proven one, so the
    make-or-break obligation (§Decision 3) is **adequacy**: the machine, driven to
    completion on ONE fiber with no concurrency op, equals [run].

    This file is the SPIKE the resolution (2026-07-22) authorized: prove adequacy on
    the [{Ret, Bind, Perform}] fragment.  If it closes cleanly, C5 commits to the CEK
    machine; if the frame-stack induction fights, C5 takes the statement-boundary
    fallback (§Risk).  SPIKE VERDICT: it closes — the generalized-over-continuation
    induction goes through by plain structural induction on [tm], no fuel, no measure
    (the [star]-relation formulation composes by transitivity).  Print Assumptions is
    "Closed under the global context".

    Scope of the spike (deliberately the 3 constructs the resolution named): [Ret]
    (pure value), [Perform] (one effect step — its semantics is REUSED from [run] so
    agreement is free), [Bind] (the sequencing that introduces the continuation
    frame — the only interesting case).  Match/Repeat/Prim/Fold are the scale-up, not
    the risk: they add frame shapes, not a new adequacy idea. *)

From Stdlib Require Import List Bool ZArith.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

(* ===== §1  The machine ====================================================== *)

(** The one frame the fragment needs: "after the focused term returns a value,
    bind it at de Bruijn 0 and run [t2] in [env]".  Bind is the only construct that
    leaves pending work; its frame is the defunctionalized continuation. *)
Inductive frame : Type := KB : tm -> list dval -> frame.
Definition kont : Type := list frame.

(** A machine configuration: either FOCUS a term (control + env + continuation +
    world), or UNWIND an outcome through the continuation. *)
Inductive config : Type :=
| CEval : tm -> list dval -> kont -> world -> config
| CRet  : outcome -> kont -> world -> config.

Definition halted (c : config) : bool :=
  match c with CRet _ [] _ => true | _ => false end.

(** ONE reduction.  [Perform]'s result is taken verbatim from [run] (Perform is a
    leaf — [run] on it is a single step), so the machine and [run] cannot disagree
    on effects by construction.  The out-of-fragment default is never reached under
    [frag] (§3). *)
Definition step (c : config) : config :=
  match c with
  | CEval t env k w =>
      match t with
      | Ret v          => CRet (ORet (eval_val env v)) k w
      | Perform o args => let '(r, w') := run env (Perform o args) w in CRet r k w'
      | Bind t1 t2     => CEval t1 env (KB t2 env :: k) w
      | _              => CRet (ORet Dstuck) k w   (* out of fragment: parked *)
      end
  | CRet r k w =>
      match k with
      | []             => CRet r [] w              (* halted: fixpoint *)
      | KB t2 env2 :: k' =>
          match r with
          | ORet x => CEval t2 (x :: env2) k' w    (* value: enter the frame body *)
          | OErr e => CRet (OErr e) k' w           (* abort: discard the frame *)
          end
      end
  end.

(** Reflexive-transitive closure of [step].  [star_step] may fire on a halted
    config too (it steps to itself), which [star_refl] closes — no stuckness. *)
Inductive star : config -> config -> Prop :=
| star_refl : forall c, star c c
| star_step : forall c c', star (step c) c' -> star c c'.

Lemma star_trans : forall a b, star a b -> forall d, star b d -> star a d.
Proof.
  intros a b Hab; induction Hab as [p | p q Hstep IH]; intros d Hbd.
  - exact Hbd.
  - apply star_step. apply IH. exact Hbd.
Qed.

(* ===== §2  The fragment ===================================================== *)

Fixpoint frag (t : tm) : bool :=
  match t with
  | Ret _        => true
  | Perform _ _  => true
  | Bind t1 t2   => frag t1 && frag t2
  | _            => false
  end.

(** [run] on the fragment's [Bind] (definitional — the reference's [Bind] arm). *)
Lemma run_bind : forall env t1 t2 w,
  run env (Bind t1 t2) w
  = match run env t1 w with
    | (ORet x, w') => run (x :: env) t2 w'
    | (OErr e, w') => (OErr e, w')
    end.
Proof. reflexivity. Qed.

(* ===== §3  ADEQUACY — the make-or-break theorem ============================= *)

(** THE generalized statement (over an arbitrary continuation [k]): evaluating [t]
    under [k] reaches the state where [t]'s [run] outcome sits on TOP of the SAME
    [k], ready to unwind.  Generalizing over [k] is what makes the [Bind] case
    compose — the frame pushed for [t2] is just a longer [k] the IH already covers.
    Plain structural induction on [t]; the [star] transitivity chains the segments.

    This is the CEK-vs-big-step adequacy that keeps the machine from being an
    unvalidated second semantics: [run] is preserved exactly. *)
Theorem cek_run : forall t, frag t = true ->
  forall env k w,
    star (CEval t env k w)
         (CRet (fst (run env t w)) k (snd (run env t w))).
Proof.
  induction t as [v | t1 IH1 t2 IH2 | o args | | | |];
    intros Hfrag env k w; cbn [frag] in Hfrag; try discriminate.
  - (* Ret v : one step to the value, k untouched *)
    apply star_step. cbn [step run fst snd]. apply star_refl.
  - (* Bind t1 t2 *)
    apply andb_true_iff in Hfrag as [H1 H2].
    apply star_step. cbn [step].
    (* evaluate t1 under the extended continuation KB t2 env :: k *)
    eapply star_trans; [ apply (IH1 H1 env (KB t2 env :: k) w) |].
    rewrite run_bind.
    destruct (run env t1 w) as [[x | e] w1] eqn:E1; cbn [fst snd].
    + (* t1 returned a value: enter the frame, run t2 *)
      apply star_step. cbn [step].
      apply (IH2 H2 (x :: env) k w1).
    + (* t1 aborted: discard the frame, propagate the error *)
      apply star_step. cbn [step]. apply star_refl.
  - (* Perform o args : one step, result verbatim from run *)
    apply star_step. cbn [step].
    destruct (run env (Perform o args) w) as [r w'] eqn:EP. cbn [fst snd].
    apply star_refl.
Qed.

(** Top-level adequacy: with the EMPTY continuation, the machine run to a halted
    state IS [run] — outcome and world.  This is the statement C5 needs: the step
    machine is a faithful evaluation strategy for every concurrency-free fiber, so
    every C0–C4 theorem transfers and concurrency is a conservative extension. *)
Corollary cek_adequate : forall t, frag t = true ->
  forall env w,
    star (CEval t env [] w)
         (CRet (fst (run env t w)) [] (snd (run env t w))).
Proof. intros t Hf env w. apply (cek_run t Hf env [] w). Qed.

(* ===== §4  Anti-vacuity: the machine really executes (a driver instance) ===== *)

(** A concrete fuel driver, so the [star] reachability above is witnessed by an
    actual multi-step computation (the relation is not vacuously satisfiable — here
    is a term whose machine takes several real steps and lands exactly on [run]). *)
Fixpoint drive (n : nat) (c : config) : config :=
  match n with
  | O    => c
  | S m  => if halted c then c else drive m (step c)
  end.

(** A three-frame fragment term: bind a pure value, then an effect (Ask), then
    return the effect's result. *)
Definition ex : tm :=
  Bind (Ret (VInt 5))
    (Bind (Perform OAsk [])
       (Ret (VVar 0%nat))).

Theorem ex_in_fragment : frag ex = true.
Proof. reflexivity. Qed.

(** The machine drives [ex] to EXACTLY [run]'s outcome and world (vm_compute), on a
    concrete initial world — the reachability of §3 made executable. *)
Theorem ex_machine_matches_run :
  drive 20%nat (CEval ex [] [] (init_world DUnit 0))
  = CRet (fst (run [] ex (init_world DUnit 0)))
         [] (snd (run [] ex (init_world DUnit 0))).
Proof. vm_compute. reflexivity. Qed.

(** ... and that shared answer is the expected value (Ask returns the ctx, DUnit). *)
Theorem ex_result :
  fst (run [] ex (init_world DUnit 0)) = ORet DUnit.
Proof. vm_compute. reflexivity. Qed.

(* ===== §5  Print Assumptions ================================================ *)

(** Each must read "Closed under the global context" — the spike is axiom-free. *)
Print Assumptions star_trans.
Print Assumptions cek_run.
Print Assumptions cek_adequate.
Print Assumptions ex_machine_matches_run.
