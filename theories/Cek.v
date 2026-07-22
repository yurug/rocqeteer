(** * Cek — C5 fiber step machine + FULL-tm adequacy (adr-0019 §Decision 2/3).

    A suspended fiber needs a continuation, but big-step [run] has none.  The answer
    (adr-0019) is a defunctionalized continuation — a frame-stack STEP MACHINE over
    the SAME [tm] (an evaluation strategy, not a second IR).  Honest only if it AGREES
    with [run]: the make-or-break obligation is **adequacy** — the machine driven to
    completion on one concurrency-free fiber equals [run].

    The C5.1 spike proved this on [{Ret, Bind, Perform}]; the induction did not fight,
    so C5 committed to the CEK machine (2026-07-22 resolution, Q3).  THIS file is the
    scale-up: adequacy over the WHOLE [tm] — [Match], [Repeat], [Prim], [Fold] added.
    As predicted, they are more frame shapes, not a new idea:
      - [Perform]/[Prim] : leaves — [step] reuses [run], agreement is free.
      - [Match]          : a pure dispatch to a single tail-run — NO frame ([select]).
      - [Bind]           : one frame [KB] (bind the value, run the tail).
      - [Repeat]         : one frame [KRep] (iters left; on return, refocus as Repeat).
      - [Fold]           : one frame [KFold] (elements left; the CRet value is the acc).
    THE theorem [cek_run] : [adeq t] for every [t], by strong structural induction with
    the continuation generalized; three list/fuel helper inductions close Match/Repeat/
    Fold.  [cek_adequate] is the empty-continuation top level: the machine IS [run], so
    every C0–C4 theorem transfers and concurrency is a conservative extension.

    Print Assumptions is "Closed under the global context" throughout. *)

From Stdlib Require Import List ZArith.
From Rocqeteer Require Import EffIR Journal.
Import ListNotations.
Local Open Scope Z_scope.

(* ===== §1  The machine ====================================================== *)

(** Frames — one per construct that leaves pending work after a sub-run.  [Match]
    and the leaves need none. *)
Inductive frame : Type :=
| KB    : tm -> list dval -> frame                 (* Bind: bind result at db0, run t2 *)
| KRep  : nat -> tm -> list dval -> frame           (* Repeat: iterations still to do *)
| KFold : list dval -> tm -> list dval -> frame.    (* Fold: elements left; CRet value = acc *)

Definition kont : Type := list frame.

Inductive config : Type :=
| CEval : tm -> list dval -> kont -> world -> config
| CRet  : outcome -> kont -> world -> config.

Definition halted (c : config) : bool :=
  match c with CRet _ [] _ => true | _ => false end.

(** [Match]'s pure dispatch: the reference's first-match-wins, as a value function
    returning the chosen (body, extended-env).  Mirrors [try_branches] (Journal.v). *)
Fixpoint select (d : dval) (env : list dval) (bs : list (pat * tm)) (default : tm)
  : tm * list dval :=
  match bs with
  | []              => (default, env)
  | (p, body) :: rest =>
      match match_pat p d with
      | Some payloads => (body, push_env payloads env)
      | None          => select d env rest default
      end
  end.

(** ONE reduction.  [Perform]/[Prim] reuse [run] verbatim (they are leaves — [run] on
    them is a single step), so the machine cannot disagree with [run] on effects or
    primitives by construction. *)
Definition step (c : config) : config :=
  match c with
  | CEval t env k w =>
      match t with
      | Ret v          => CRet (ORet (eval_val env v)) k w
      | Perform o args => let '(r, w') := run env (Perform o args) w in CRet r k w'
      | Prim p args    => let '(r, w') := run env (Prim p args) w in CRet r k w'
      | Bind t1 t2     => CEval t1 env (KB t2 env :: k) w
      | Match scrut branches default =>
          let '(body, env') := select (eval_val env scrut) env branches default in
          CEval body env' k w
      | Repeat n body =>
          match n with
          | O    => CRet (ORet DUnit) k w
          | S m  => CEval body env (KRep m body env :: k) w
          end
      | Fold lst init body =>
          CEval init env
            (KFold (match eval_val env lst with DList vs => vs | _ => [] end)
               body env :: k) w
      end
  | CRet r k w =>
      match k with
      | []             => CRet r [] w
      | KB t2 env2 :: k' =>
          match r with
          | ORet x => CEval t2 (x :: env2) k' w
          | OErr e => CRet (OErr e) k' w
          end
      | KRep m body env :: k' =>
          match r with
          | ORet _ => CEval (Repeat m body) env k' w    (* refocus: run the rest *)
          | OErr e => CRet (OErr e) k' w
          end
      | KFold xs body env :: k' =>
          match r with
          | OErr e => CRet (OErr e) k' w
          | ORet acc =>
              match xs with
              | []       => CRet (ORet acc) k' w
              | x :: xs' => CEval body (push_env [x; acc] env)
                              (KFold xs' body env :: k') w
              end
          end
      end
  end.

Inductive star : config -> config -> Prop :=
| star_refl : forall c, star c c
| star_step : forall c c', star (step c) c' -> star c c'.

Lemma star_trans : forall a b, star a b -> forall d, star b d -> star a d.
Proof.
  intros a b Hab; induction Hab as [p | p q Hstep IH]; intros d Hbd.
  - exact Hbd.
  - apply star_step. apply IH. exact Hbd.
Qed.

(** Adequacy of a single term, generalized over the continuation [k]: evaluating [t]
    under [k] reaches the state with [t]'s [run] outcome on top of the SAME [k]. *)
Definition adeq (t : tm) : Prop :=
  forall env k w,
    star (CEval t env k w) (CRet (fst (run env t w)) k (snd (run env t w))).

(* ===== §2  Definitional step equations (all by reflexivity) ================= *)

Lemma run_bind : forall env t1 t2 w,
  run env (Bind t1 t2) w
  = match run env t1 w with
    | (ORet x, w') => run (x :: env) t2 w'
    | (OErr e, w') => (OErr e, w')
    end.
Proof. reflexivity. Qed.

Lemma tb_nil : forall env d default w,
  try_branches env d default w [] = run env default w.
Proof. reflexivity. Qed.

Lemma tb_cons : forall env d default w p body rest,
  try_branches env d default w ((p, body) :: rest)
  = match match_pat p d with
    | Some payloads => run (push_env payloads env) body w
    | None          => try_branches env d default w rest
    end.
Proof. reflexivity. Qed.

Lemma repeat_loop_S : forall env body m w,
  repeat_loop env body (S m) w
  = match run env body w with
    | (ORet _, w1) => repeat_loop env body m w1
    | (OErr e, w1) => (OErr e, w1)
    end.
Proof. reflexivity. Qed.

Lemma fold_elems_cons : forall env body x xs acc w,
  fold_elems env body (x :: xs) acc w
  = match run (push_env [x; acc] env) body w with
    | (ORet acc', w1) => fold_elems env body xs acc' w1
    | (OErr e, w1)    => (OErr e, w1)
    end.
Proof. reflexivity. Qed.

(* ===== §3  Helper inductions: Match dispatch, Repeat fuel, Fold elements ===== *)

(** The chosen branch is adequate: [select] lands on a body/default that agrees with
    [try_branches] under any continuation.  Induction on the branch list. *)
Lemma cek_match_dispatch : forall bs d env default k w,
  Forall (fun pb => adeq (snd pb)) bs -> adeq default ->
  star (CEval (fst (select d env bs default)) (snd (select d env bs default)) k w)
       (CRet (fst (try_branches env d default w bs)) k
             (snd (try_branches env d default w bs))).
Proof.
  induction bs as [| [p body] rest IH]; intros d env default k w HF Hd.
  - cbn [select]. rewrite tb_nil. exact (Hd env k w).
  - cbn [select]. rewrite tb_cons.
    destruct (match_pat p d) as [payloads |] eqn:Emp; cbn [fst snd].
    + pose proof (Forall_inv HF) as Hhead; cbn [snd] in Hhead.
      exact (Hhead (push_env payloads env) k w).
    + exact (IH d env default k w (Forall_inv_tail HF) Hd).
Qed.

(** Bounded loop: the [KRep] frame, run to the end, is [repeat_loop].  Induction on
    the fuel. *)
Lemma cek_repeat : forall body, adeq body ->
  forall n env k w,
    star (CEval (Repeat n body) env k w)
         (CRet (fst (repeat_loop env body n w)) k (snd (repeat_loop env body n w))).
Proof.
  intros body Hb; induction n as [| m IH]; intros env k w.
  - apply star_step. cbn [step]. apply star_refl.
  - apply star_step. cbn [step].
    eapply star_trans; [ apply (Hb env (KRep m body env :: k) w) |].
    destruct (run env body w) as [[x | e] w1] eqn:Eb; cbn [fst snd].
    + apply star_step. cbn [step].
      rewrite repeat_loop_S, Eb. apply (IH env k w1).
    + apply star_step. cbn [step].
      rewrite repeat_loop_S, Eb. apply star_refl.
Qed.

(** Fold body over the element list: the [KFold] frame, from an accumulator value,
    is [fold_elems].  Induction on the elements. *)
Lemma cek_fold : forall body, adeq body ->
  forall xs env acc k w,
    star (CRet (ORet acc) (KFold xs body env :: k) w)
         (CRet (fst (fold_elems env body xs acc w)) k
               (snd (fold_elems env body xs acc w))).
Proof.
  intros body Hb; induction xs as [| x xs' IH]; intros env acc k w.
  - apply star_step. cbn [step]. apply star_refl.
  - apply star_step. cbn [step].
    eapply star_trans;
      [ apply (Hb (push_env [x; acc] env) (KFold xs' body env :: k) w) |].
    destruct (run (push_env [x; acc] env) body w) as [[acc' | e] w1] eqn:Er;
      cbn [fst snd].
    + rewrite fold_elems_cons, Er. apply (IH env acc' k w1).
    + apply star_step. cbn [step]. rewrite fold_elems_cons, Er. apply star_refl.
Qed.

(* ===== §4  ADEQUACY over the FULL tm ======================================== *)

Theorem cek_run : forall t, adeq t.
Proof.
  apply tm_ind_strong.
  - (* Ret *)
    intros v env k w. apply star_step. cbn [step run fst snd]. apply star_refl.
  - (* Bind *)
    intros t1 t2 IH1 IH2 env k w. apply star_step. cbn [step].
    eapply star_trans; [ apply (IH1 env (KB t2 env :: k) w) |].
    rewrite run_bind. destruct (run env t1 w) as [[x | e] w1] eqn:E1; cbn [fst snd].
    + apply star_step. cbn [step]. apply (IH2 (x :: env) k w1).
    + apply star_step. cbn [step]. apply star_refl.
  - (* Perform *)
    intros o args env k w. apply star_step. cbn [step].
    destruct (run env (Perform o args) w) as [r w'] eqn:EP. cbn [fst snd].
    apply star_refl.
  - (* Match *)
    intros scrut branches default HF Hd env k w.
    apply star_step. cbn [step].
    destruct (select (eval_val env scrut) env branches default) as [body env'] eqn:Es.
    rewrite run_match_eq.
    pose proof (cek_match_dispatch branches (eval_val env scrut) env default k w HF Hd)
      as Hdisp.
    rewrite Es in Hdisp; cbn [fst snd] in Hdisp. exact Hdisp.
  - (* Repeat *)
    intros n body Hb env k w. rewrite run_repeat_eq. exact (cek_repeat body Hb n env k w).
  - (* Prim *)
    intros p args env k w. apply star_step. cbn [step].
    destruct (run env (Prim p args) w) as [r w'] eqn:EP. cbn [fst snd].
    apply star_refl.
  - (* Fold *)
    intros lst init body Hi Hb env k w. apply star_step. cbn [step].
    rewrite run_fold_eq.
    eapply star_trans;
      [ apply (Hi env
                 (KFold (match eval_val env lst with DList vs => vs | _ => [] end)
                    body env :: k) w) |].
    destruct (run env init w) as [[acc0 | e] w'] eqn:Ei; cbn [fst snd].
    + assert (Hvs : fold_elems env body
                      (match eval_val env lst with DList vs => vs | _ => [] end)
                      acc0 w'
                    = match eval_val env lst with
                      | DList vs => fold_elems env body vs acc0 w'
                      | _        => (ORet acc0, w')
                      end)
        by (destruct (eval_val env lst); reflexivity).
      rewrite <- Hvs.
      apply (cek_fold body Hb
               (match eval_val env lst with DList vs => vs | _ => [] end)
               env acc0 k w').
    + apply star_step. cbn [step]. apply star_refl.
Qed.

(** TOP-LEVEL ADEQUACY (empty continuation): the step machine run to a halted state
    IS big-step [run], on outcome AND world, for EVERY program.  This is the C5 pillar
    — the machine is a faithful evaluation strategy for every concurrency-free fiber,
    so the proven oracle is preserved and concurrency is a conservative extension. *)
Corollary cek_adequate : forall t env w,
  star (CEval t env [] w) (CRet (fst (run env t w)) [] (snd (run env t w))).
Proof. intros t env w. apply (cek_run t env [] w). Qed.

(* ===== §5  Anti-vacuity: the machine really executes (driver instance) ====== *)

Fixpoint drive (n : nat) (c : config) : config :=
  match n with
  | O   => c
  | S m => if halted c then c else drive m (step c)
  end.

(** A term spanning every construct class: bind the context, run a bounded loop with
    an effect, then a Fold-with-Prim over a value list — Repeat, Fold, Match-free but
    Prim/Perform/Bind/Ret all present.  The machine drives it to EXACTLY [run]. *)
Definition ex : tm :=
  Bind (Perform OAsk [])
    (Bind (Repeat 3%nat (Perform OTrace [VInt 7]))
       (Fold (VList [VInt 1; VInt 2]) (Ret (VInt 0))
          (Prim PAddChecked [VVar 0%nat; VVar 1%nat]))).

Theorem ex_machine_matches_run :
  drive 40%nat (CEval ex [] [] (init_world DUnit 0))
  = CRet (fst (run [] ex (init_world DUnit 0)))
         [] (snd (run [] ex (init_world DUnit 0))).
Proof. vm_compute. reflexivity. Qed.

(* ===== §6  Print Assumptions ================================================ *)

(** Each must read "Closed under the global context" — the machine is axiom-free. *)
Print Assumptions star_trans.
Print Assumptions cek_match_dispatch.
Print Assumptions cek_repeat.
Print Assumptions cek_fold.
Print Assumptions cek_run.
Print Assumptions cek_adequate.
Print Assumptions ex_machine_matches_run.
