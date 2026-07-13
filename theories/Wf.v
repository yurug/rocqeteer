(** * Wf — R10 v1: the PROVEN well-formedness checker (adr-0014-wf-checker).

    [wf_tm : nat -> tm -> bool] checks, structurally and WITHOUT a value-type universe:
    de Bruijn scope (every [VVar i] satisfies [i < depth], through [Bind] (+1), [Match]
    branch binders (+ [pat_binders p]), [Fold] bodies (+2)), exact [Perform]/[Prim]
    arities, and recursion into [VSome]/[VSucc]/[VPair]/[VTag]/[VList] payloads.

    THE SOUNDNESS THEOREM ([wf_no_scope_stuck]): for [wf_tm (length env) t = true],
    evaluation never takes the out-of-scope [VVar] branch — formalized via an
    instrumented twin [run_checked] over [eval_val_checked] (which returns [None]
    EXACTLY on a scope miss, i.e. [nth_error] failure, and mirrors [run] everywhere
    else) that is proven to return [Some (run env t w)] on wf programs: it never hits
    the [None] marker and agrees with [run] in all observables. SHAPE errors (e.g.
    [VSucc] of a non-int, prim argument shapes, non-[DList] [Fold] scrutinees) remain
    dynamic and are NOT claimed — this file proves well-FORMEDNESS, never
    well-TYPEDness (adr-0014 §3/§5).

    Anti-vacuity (adr-0014 §3):
    - a concrete ill-scoped program ([VVar 2] under one binder) that [wf_tm] rejects
      AND whose run hits [Dstuck], while [run_checked] returns the [None] marker;
    - a MUTANT checker whose [Fold] clause skips the (+2)-extended body check: it
      ACCEPTS a program whose run produces [Dstuck]-tainted output, observably
      different from a correct twin (any depth-REDUCING mutation is strictly stricter
      and provably cannot accept a stuck program — that direction is instead caught by
      the inhabitance theorem, demonstrated on a second, no-extension mutant);
    - inhabitance: [wf_tm 0] accepts EVERY program of the single-source
      [Samples.all_programs] list ([wf_all_programs], vm_compute).

    The extracted [wf_tm] is the codegen gate (adr-0014 §4): one implementation, two
    uses — proof subject here, pre-emission CI gate in codegen/emit.ml. Witnesses are
    EXPLICIT (theories/Prims.v header note); Print Assumptions must read "Closed under
    the global context" for every theorem. *)

From Stdlib Require Import ZArith List String Ascii Bool Lia.
From Rocqeteer Require Import EffIR Samples Journal.
Import ListNotations.
Local Open Scope Z_scope.

(** [String] is imported (for [Samples]); make the bare [length] the LIST one. *)
Local Notation length := List.length.

(* ===== §1  The checker ====================================================== *)

(** Exact arity of each effect operation (adr-0014 §2; the adr-0011/0013 op table). *)
Definition op_arity (o : op) : nat :=
  match o with
  | OGet         => 1
  | OPut         => 2
  | ODelete      => 1
  | OGetDeadline => 1
  | OSetDeadline => 2
  | ONow         => 0
  | OThrow       => 1
  | OAsk         => 0
  | OTrace       => 1
  | OCacheGet    => 1
  | OCachePut    => 2
  | OJournal     => 1
  end%nat.

(** Exact arity of each primitive (the adr-0009/0012 registry). The exhaustive match
    makes forgetting a new prim's row a compile error (adr-0014 §Consequences). *)
Definition prim_arity (p : prim) : nat :=
  match p with
  | PAddChecked  => 2
  | PSubChecked  => 2
  | PCmpInt      => 2
  | PEqBytes     => 2
  | PBytesLen    => 1
  | PBytesConcat => 2
  | PBytesSub    => 3
  | PParseInt64  => 1
  | PPrintInt    => 1
  | PMulChecked  => 2
  | PListLen     => 1
  | PListNth     => 2
  | PDivFloor    => 2
  | PLowerBytes  => 1
  | PUpperBytes  => 1
  | PListSnoc    => 2
  end%nat.

(** Binder count of each depth-1 pattern — exactly the length of the payload list
    [match_pat] returns on success ([match_pat_binders] below). *)
Definition pat_binders (p : pat) : nat :=
  match p with
  | PUnit | PBool _ | PInt _ | PBytes _ | PNone => 0
  | PSome  => 1
  | PPair  => 2
  | PTag _ => 1
  end%nat.

(** [wf_val depth v]: every [VVar i] in [v] satisfies [i < depth]; recurses into all
    payload positions. The [VList] nested fix is the [eval_val] guardedness technique. *)
Fixpoint wf_val (depth : nat) (v : val) : bool :=
  match v with
  | VVar i    => Nat.ltb i depth
  | VUnit | VBool _ | VInt _ | VNone | VZero | VBytes _ => true
  | VSome a   => wf_val depth a
  | VSucc a   => wf_val depth a
  | VPair a b => wf_val depth a && wf_val depth b
  | VTag _ a  => wf_val depth a
  | VList vs  =>
      (fix wf_list (xs : list val) : bool :=
         match xs with
         | []       => true
         | x :: xs' => wf_val depth x && wf_list xs'
         end) vs
  end.

(** [wf_tm depth t]: well-formedness at binding depth [depth] (adr-0014 §2) —
    scope through the binder-introducing constructs ([Bind] +1, [Match] branch bodies
    + [pat_binders], [Fold] body +2), exact [Perform]/[Prim] arities via [Nat.eqb] on
    the argument-list length, and [wf_val] on every val position. *)
Fixpoint wf_tm (depth : nat) (t : tm) : bool :=
  match t with
  | Ret v          => wf_val depth v
  | Bind t1 t2     => wf_tm depth t1 && wf_tm (S depth) t2
  | Perform o args =>
      Nat.eqb (length args) (op_arity o) && forallb (wf_val depth) args
  | Match scrut branches default =>
      wf_val depth scrut
      && (fix wf_bs (bs : list (pat * tm)) : bool :=
            match bs with
            | []                => true
            | (p, body) :: rest =>
                wf_tm (pat_binders p + depth)%nat body && wf_bs rest
            end) branches
      && wf_tm depth default
  | Repeat _ body  => wf_tm depth body
  | Prim p args    =>
      Nat.eqb (length args) (prim_arity p) && forallb (wf_val depth) args
  | Fold lst init body =>
      wf_val depth lst && wf_tm depth init && wf_tm (S (S depth)) body
  end.

(** Named twin of [wf_tm]'s branch-list nested fix + its definitional equation, so
    proofs can speak about it (the Journal.v twin technique). *)
Definition wf_branches (depth : nat) :=
  fix wf_bs (bs : list (pat * tm)) : bool :=
    match bs with
    | []                => true
    | (p, body) :: rest =>
        wf_tm (pat_binders p + depth)%nat body && wf_bs rest
    end.

Lemma wf_tm_match_eq : forall depth scrut branches default,
  wf_tm depth (Match scrut branches default)
  = wf_val depth scrut && wf_branches depth branches && wf_tm depth default.
Proof. reflexivity. Qed.

(* ===== §2  The instrumented evaluator: None EXACTLY on a scope miss ========= *)

(** [eval_val_checked env v]: same recursion structure as [eval_val], but the
    out-of-scope [VVar] branch is syntactically distinguishable — [nth_error] returns
    [None] exactly when [n >= length env] (adr-0014 §implementers). Every OTHER case
    mirrors [eval_val] verbatim; in particular the [VSucc]-of-non-int SHAPE error still
    yields [Some Dstuck] (a value, not the scope marker) — shape errors are not
    claimed. *)
Fixpoint eval_val_checked (env : list dval) (v : val) : option dval :=
  match v with
  | VVar n    => nth_error env n
  | VUnit     => Some DUnit
  | VBool b   => Some (DBool b)
  | VInt z    => Some (DInt z)
  | VNone     => Some DNone
  | VSome a   => match eval_val_checked env a with
                 | Some d => Some (DSome d)
                 | None   => None
                 end
  | VPair a b => match eval_val_checked env a, eval_val_checked env b with
                 | Some da, Some db => Some (DPair da db)
                 | _, _             => None
                 end
  | VZero     => Some (DInt 0)
  | VSucc a   => match eval_val_checked env a with
                 | Some (DInt z) => Some (DInt (Z.succ z))
                 | Some _        => Some Dstuck   (* SHAPE error, not a scope miss *)
                 | None          => None
                 end
  | VBytes bs => Some (DBytes bs)
  | VTag z a  => match eval_val_checked env a with
                 | Some d => Some (DTag z d)
                 | None   => None
                 end
  | VList vs  =>
      match (fix eval_list (xs : list val) : option (list dval) :=
               match xs with
               | []       => Some []
               | x :: xs' => match eval_val_checked env x, eval_list xs' with
                             | Some d, Some ds => Some (d :: ds)
                             | _, _            => None
                             end
               end) vs with
      | Some ds => Some (DList ds)
      | None    => None
      end
  end.

(** Checked evaluation of an argument list ([Perform]/[Prim] positions). *)
Fixpoint eval_vals_checked (env : list dval) (xs : list val) : option (list dval) :=
  match xs with
  | []       => Some []
  | x :: xs' => match eval_val_checked env x, eval_vals_checked env xs' with
                | Some d, Some ds => Some (d :: ds)
                | _, _            => None
                end
  end.

(** Named twins of the two [VList] nested fixes + definitional equations. *)
Definition eval_list_checked (env : list dval) :=
  fix eval_list (xs : list val) : option (list dval) :=
    match xs with
    | []       => Some []
    | x :: xs' => match eval_val_checked env x, eval_list xs' with
                  | Some d, Some ds => Some (d :: ds)
                  | _, _            => None
                  end
    end.

Lemma eval_val_checked_vlist_eq : forall env vs,
  eval_val_checked env (VList vs)
  = match eval_list_checked env vs with
    | Some ds => Some (DList ds)
    | None    => None
    end.
Proof. reflexivity. Qed.

Definition eval_list_ref (env : list dval) :=
  fix eval_list (xs : list val) : list dval :=
    match xs with
    | []       => []
    | x :: xs' => eval_val env x :: eval_list xs'
    end.

Lemma eval_val_vlist_eq : forall env vs,
  eval_val env (VList vs) = DList (eval_list_ref env vs).
Proof. reflexivity. Qed.

Definition wf_val_list (depth : nat) :=
  fix wf_list (xs : list val) : bool :=
    match xs with
    | []       => true
    | x :: xs' => wf_val depth x && wf_list xs'
    end.

Lemma wf_val_vlist_eq : forall depth vs,
  wf_val depth (VList vs) = wf_val_list depth vs.
Proof. reflexivity. Qed.

(* ===== §3  Value-level soundness: (a) totality + (b) agreement in one ======= *)

(** Strengthened induction principle for [val]: the stock one gives no hypothesis for
    the [VList] elements (the Journal.v [tm_ind_strong] technique). *)
Fixpoint val_ind_strong (P : val -> Prop)
    (HVar   : forall n, P (VVar n))
    (HUnit  : P VUnit)
    (HBool  : forall b, P (VBool b))
    (HInt   : forall z, P (VInt z))
    (HNone  : P VNone)
    (HSome  : forall a, P a -> P (VSome a))
    (HPair  : forall a b, P a -> P b -> P (VPair a b))
    (HZero  : P VZero)
    (HSucc  : forall a, P a -> P (VSucc a))
    (HBytes : forall bs, P (VBytes bs))
    (HTag   : forall z a, P a -> P (VTag z a))
    (HList  : forall vs, Forall P vs -> P (VList vs))
    (v : val) {struct v} : P v :=
  let F := val_ind_strong P HVar HUnit HBool HInt HNone HSome HPair HZero HSucc
                          HBytes HTag HList in
  match v with
  | VVar n    => HVar n
  | VUnit     => HUnit
  | VBool b   => HBool b
  | VInt z    => HInt z
  | VNone     => HNone
  | VSome a   => HSome a (F a)
  | VPair a b => HPair a b (F a) (F b)
  | VZero     => HZero
  | VSucc a   => HSucc a (F a)
  | VBytes bs => HBytes bs
  | VTag z a  => HTag z a (F a)
  | VList vs  =>
      HList vs ((fix elems_ind (l : list val) : Forall P l :=
                   match l with
                   | []      => Forall_nil _
                   | x :: l' => Forall_cons x (F x) (elems_ind l')
                   end) vs)
  end.

(** In-scope lookup: [nth_error] agrees with the defaulted [nth] below the length. *)
Lemma nth_error_lt_length : forall (l : list dval) (n : nat),
  Nat.ltb n (length l) = true ->
  nth_error l n = Some (nth n l Dstuck).
Proof.
  induction l as [| x l' IH]; intros n H; cbn in H.
  - destruct n; discriminate.
  - destruct n as [| n']; cbn; [reflexivity | apply IH; exact H].
Qed.

(** THE value-level lemma — (a) totality and (b) agreement in one statement: a wf val
    checks out to [Some] of exactly the reference evaluation (so the out-of-scope
    branch, the only [None] source, is never taken). *)
Lemma eval_val_checked_wf : forall env v,
  wf_val (length env) v = true ->
  eval_val_checked env v = Some (eval_val env v).
Proof.
  intros env v; revert v.
  apply (val_ind_strong (fun v =>
           wf_val (length env) v = true ->
           eval_val_checked env v = Some (eval_val env v))).
  - (* VVar *) intros n H; cbn in H |- *. apply nth_error_lt_length; exact H.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* VSome *) intros a IH H; cbn in H |- *. rewrite (IH H). reflexivity.
  - (* VPair *)
    intros a b IHa IHb H; cbn in H |- *.
    apply andb_true_iff in H as [Ha Hb].
    rewrite (IHa Ha), (IHb Hb). reflexivity.
  - reflexivity.
  - (* VSucc *)
    intros a IH H; cbn in H |- *. rewrite (IH H).
    destruct (eval_val env a); reflexivity.
  - reflexivity.
  - (* VTag *) intros z a IH H; cbn in H |- *. rewrite (IH H). reflexivity.
  - (* VList *)
    intros vs HF H.
    rewrite wf_val_vlist_eq in H.
    rewrite eval_val_checked_vlist_eq, eval_val_vlist_eq.
    enough (E : eval_list_checked env vs = Some (eval_list_ref env vs))
      by (rewrite E; reflexivity).
    induction HF as [| x xs Px HFxs IH]; cbn in H |- *.
    + reflexivity.
    + apply andb_true_iff in H as [Hx Hxs].
      rewrite (Px Hx), (IH Hxs). reflexivity.
Qed.

(** Corollary, the (a) reading: on wf vals the checked evaluator never hits the
    scope-miss marker. *)
Corollary eval_val_checked_total : forall env v,
  wf_val (length env) v = true ->
  eval_val_checked env v <> None.
Proof.
  intros env v H; rewrite (eval_val_checked_wf env v H); discriminate.
Qed.

(** Argument lists: checked evaluation is [Some] of the reference [map]. *)
Lemma eval_vals_checked_wf : forall env args,
  forallb (wf_val (length env)) args = true ->
  eval_vals_checked env args = Some (map (eval_val env) args).
Proof.
  intros env args; induction args as [| a args IH]; intros H; cbn in H |- *.
  - reflexivity.
  - apply andb_true_iff in H as [Ha Hargs].
    rewrite (eval_val_checked_wf env a Ha), (IH Hargs). reflexivity.
Qed.

(* ===== §4  Environment-shape lemmas ========================================= *)

(** The KEY depth-invariant lemma: pushing payloads extends the env by exactly their
    count. *)
Lemma push_env_length : forall (vs env : list dval),
  length (push_env vs env) = (length vs + length env)%nat.
Proof.
  unfold push_env; induction vs as [| v vs IH]; intros env; cbn.
  - reflexivity.
  - rewrite IH; cbn; lia.
Qed.

(** [pat_binders] is exactly the payload count [match_pat] delivers on success — the
    checker's branch-depth extension matches the interpreter's env extension. *)
Lemma match_pat_binders : forall p d payloads,
  match_pat p d = Some payloads ->
  length payloads = pat_binders p.
Proof.
  intros p d payloads H; destruct p, d; cbn in H; try discriminate;
    repeat match goal with
           | H : (if ?b then _ else _) = Some _ |- _ => destruct b; try discriminate
           end;
    injection H as H; subst; reflexivity.
Qed.

(* ===== §5  The instrumented run and its named twins ========================= *)

(** [run_checked env t w]: the twin of [run] over [eval_val_checked] — same recursion
    structure, same world threading, same short-circuits; returns [None] EXACTLY when
    some val evaluation the run performs hits the out-of-scope [VVar] branch. Every
    non-scope behavior (shape [Dstuck]s included) mirrors [run] verbatim. *)
Fixpoint run_checked (env : list dval) (t : tm) (w : world) : option (outcome * world) :=
  match t with
  | Ret v =>
      match eval_val_checked env v with
      | Some d => Some (ORet d, w)
      | None   => None
      end
  | Bind t1 t2 =>
      match run_checked env t1 w with
      | Some (ORet x, w') => run_checked (x :: env) t2 w'
      | Some (OErr e, w') => Some (OErr e, w')
      | None              => None
      end
  | Perform o args =>
      match eval_vals_checked env args with
      | None    => None
      | Some vs =>
          Some (match o with
                | OThrow => (OErr (nth 0 vs Dstuck), w)
                | OAsk   => (ORet w.(ctx), w)
                | ONow   => (ORet (DInt w.(now_ms)), w)
                | OTrace => match vs with
                            | [v] => (ORet DUnit, set_trace w (v :: w.(trace)))
                            | _   => (ORet Dstuck, w)
                            end
                | OCacheGet =>
                    match vs with
                    | [DBytes kb] =>
                        (ORet (opt_to_dval (M.find (string_of_list_ascii kb) w.(cache))), w)
                    | _ => (ORet Dstuck, w)
                    end
                | OCachePut =>
                    match vs with
                    | [DBytes kb; v] =>
                        (ORet DUnit,
                         set_cache w (M.add (string_of_list_ascii kb) v w.(cache)))
                    | _ => (ORet Dstuck, w)
                    end
                | OJournal =>
                    match vs with
                    | [v] => (ORet DUnit, set_journal w ((w.(now_ms), v) :: w.(journal)))
                    | _   => (ORet Dstuck, w)
                    end
                | _ =>
                    let '(r, s') := handle_store w.(now_ms) o vs w.(kv) in
                    (ORet r, set_kv w s')
                end)
      end
  | Match scrut branches default =>
      match eval_val_checked env scrut with
      | None   => None
      | Some d =>
          (fix try_bs (bs : list (pat * tm)) {struct bs} : option (outcome * world) :=
             match bs with
             | []                => run_checked env default w
             | (p, body) :: rest =>
                 match match_pat p d with
                 | Some payloads => run_checked (push_env payloads env) body w
                 | None          => try_bs rest
                 end
             end) branches
      end
  | Repeat n body =>
      (fix loop (m : nat) (w0 : world) {struct m} : option (outcome * world) :=
         match m with
         | O    => Some (ORet DUnit, w0)
         | S m' => match run_checked env body w0 with
                   | Some (ORet _, w1) => loop m' w1
                   | Some (OErr e, w1) => Some (OErr e, w1)
                   | None              => None
                   end
         end) n w
  | Prim p args =>
      match eval_vals_checked env args with
      | Some vs => Some (ORet (apply_prim p vs), w)
      | None    => None
      end
  | Fold lst init body =>
      match eval_val_checked env lst with
      | None   => None
      | Some d =>
          match run_checked env init w with
          | None              => None
          | Some (OErr e, w') => Some (OErr e, w')
          | Some (ORet acc0, w') =>
              match d with
              | DList vs =>
                  (fix fe (xs : list dval) (acc : dval) (w0 : world) {struct xs}
                     : option (outcome * world) :=
                     match xs with
                     | []       => Some (ORet acc, w0)
                     | x :: xs' =>
                         match run_checked (push_env [x; acc] env) body w0 with
                         | Some (ORet acc', w1) => fe xs' acc' w1
                         | Some (OErr e, w1)    => Some (OErr e, w1)
                         | None                 => None
                         end
                     end) vs acc0 w'
              | _ => Some (ORet acc0, w')
              end
          end
      end
  end.

(** Named twins of [run_checked]'s nested fixes + definitional equations (the
    Journal.v technique; the reference-side twins [try_branches]/[repeat_loop]/
    [fold_elems] and their [run_*_eq] equations come from Journal.v). *)
Definition try_branches_checked (env : list dval) (d : dval) (default : tm) (w : world) :=
  fix try_bs (bs : list (pat * tm)) : option (outcome * world) :=
    match bs with
    | []                => run_checked env default w
    | (p, body) :: rest =>
        match match_pat p d with
        | Some payloads => run_checked (push_env payloads env) body w
        | None          => try_bs rest
        end
    end.

Lemma run_checked_match_eq : forall env scrut branches default w,
  run_checked env (Match scrut branches default) w
  = match eval_val_checked env scrut with
    | None   => None
    | Some d => try_branches_checked env d default w branches
    end.
Proof. reflexivity. Qed.

Definition repeat_loop_checked (env : list dval) (body : tm) :=
  fix loop (m : nat) (w0 : world) {struct m} : option (outcome * world) :=
    match m with
    | O    => Some (ORet DUnit, w0)
    | S m' => match run_checked env body w0 with
              | Some (ORet _, w1) => loop m' w1
              | Some (OErr e, w1) => Some (OErr e, w1)
              | None              => None
              end
    end.

Lemma run_checked_repeat_eq : forall env n body w,
  run_checked env (Repeat n body) w = repeat_loop_checked env body n w.
Proof. reflexivity. Qed.

Definition fold_elems_checked (env : list dval) (body : tm) :=
  fix fe (xs : list dval) (acc : dval) (w0 : world) {struct xs}
    : option (outcome * world) :=
    match xs with
    | []       => Some (ORet acc, w0)
    | x :: xs' =>
        match run_checked (push_env [x; acc] env) body w0 with
        | Some (ORet acc', w1) => fe xs' acc' w1
        | Some (OErr e, w1)    => Some (OErr e, w1)
        | None                 => None
        end
    end.

Lemma run_checked_fold_eq : forall env lst init body w,
  run_checked env (Fold lst init body) w
  = match eval_val_checked env lst with
    | None   => None
    | Some d =>
        match run_checked env init w with
        | None              => None
        | Some (OErr e, w') => Some (OErr e, w')
        | Some (ORet acc0, w') =>
            match d with
            | DList vs => fold_elems_checked env body vs acc0 w'
            | _        => Some (ORet acc0, w')
            end
        end
    end.
Proof. reflexivity. Qed.

(* ===== §6  Lifting through run: the per-construct lemmas ==================== *)

(** Branch dispatch: if every branch body and the default agree (at their EXTENDED
    depths), so does the whole first-match-wins chain. The depth bookkeeping is
    [match_pat_binders] + [push_env_length]. *)
Lemma try_branches_checked_agrees :
  forall branches env d default w,
    Forall (fun pb => forall env' w',
              wf_tm (length env') (snd pb) = true ->
              run_checked env' (snd pb) w' = Some (run env' (snd pb) w')) branches ->
    (forall env' w',
        wf_tm (length env') default = true ->
        run_checked env' default w' = Some (run env' default w')) ->
    wf_branches (length env) branches = true ->
    wf_tm (length env) default = true ->
    try_branches_checked env d default w branches
    = Some (try_branches env d default w branches).
Proof.
  induction branches as [| [p body] rest IHrest];
    intros env d default w HF Hdef Hwb Hwd.
  - cbn. apply Hdef; exact Hwd.
  - inversion HF as [| ? ? Hbody HFrest]; subst.
    cbn in Hwb. apply andb_true_iff in Hwb as [Hwbody Hwrest].
    cbn. destruct (match_pat p d) as [payloads |] eqn:Emp.
    + apply (Hbody (push_env payloads env) w).
      rewrite push_env_length, (match_pat_binders p d payloads Emp).
      exact Hwbody.
    + apply IHrest; assumption.
Qed.

(** Bounded loops: the env (hence the depth) is invariant across iterations. *)
Lemma repeat_loop_checked_agrees :
  forall env body,
    (forall env' w',
        wf_tm (length env') body = true ->
        run_checked env' body w' = Some (run env' body w')) ->
    wf_tm (length env) body = true ->
    forall n w,
      repeat_loop_checked env body n w = Some (repeat_loop env body n w).
Proof.
  intros env body Hb Hwf; induction n as [| m IH]; intros w; cbn.
  - reflexivity.
  - rewrite (Hb env w Hwf).
    destruct (run env body w) as [[x | e] w1]; [apply IH | reflexivity].
Qed.

(** One-step unfoldings of the two fold twins (definitional), so the induction can
    rewrite without [cbn] unfolding [push_env] underneath. *)
Lemma fold_elems_checked_cons : forall env body x xs acc w,
  fold_elems_checked env body (x :: xs) acc w
  = match run_checked (push_env [x; acc] env) body w with
    | Some (ORet acc', w1) => fold_elems_checked env body xs acc' w1
    | Some (OErr e, w1)    => Some (OErr e, w1)
    | None                 => None
    end.
Proof. reflexivity. Qed.

Lemma fold_elems_cons : forall env body x xs acc w,
  fold_elems env body (x :: xs) acc w
  = match run (push_env [x; acc] env) body w with
    | (ORet acc', w1) => fold_elems env body xs acc' w1
    | (OErr e, w1)    => (OErr e, w1)
    end.
Proof. reflexivity. Qed.

(** Fold iterations: each body run extends the env by EXACTLY 2 ([push_env [x; acc]]),
    matching the checker's (+2). *)
Lemma fold_elems_checked_agrees :
  forall env body,
    (forall env' w',
        wf_tm (length env') body = true ->
        run_checked env' body w' = Some (run env' body w')) ->
    wf_tm (S (S (length env))) body = true ->
    forall vs acc w,
      fold_elems_checked env body vs acc w = Some (fold_elems env body vs acc w).
Proof.
  intros env body Hb Hwf; induction vs as [| x xs IH]; intros acc w.
  - reflexivity.
  - rewrite fold_elems_checked_cons, fold_elems_cons.
    rewrite (Hb (push_env [x; acc] env) w)
      by (rewrite push_env_length; exact Hwf).
    destruct (run (push_env [x; acc] env) body w) as [[acc' | e] w1];
      [apply IH | reflexivity].
Qed.

(* ===== §7  THE SOUNDNESS THEOREM (adr-0014 §3) ============================== *)

(** For [wf_tm (length env) t = true], evaluation never takes the out-of-scope [VVar]
    branch — no scope-[Dstuck] in [eval_val] anywhere in the run of [t]: the
    instrumented [run_checked] (whose ONLY [None] source is that branch) never returns
    the [None] marker and agrees with [run] in all observables. SHAPE errors ([VSucc]
    of a non-int, prim argument shapes, non-[DList] [Fold] scrutinees) remain dynamic
    and are NOT claimed. Proof: induction on [tm] ([tm_ind_strong], Journal.v) with
    the depth invariant [depth = length env]; [Bind]/[Match]/[Fold] extend the env by
    exactly the checked amounts (+1 / [pat_binders] via [match_pat_binders] +
    [push_env_length] / +2). *)
Theorem wf_no_scope_stuck : forall t env w,
  wf_tm (length env) t = true ->
  run_checked env t w = Some (run env t w).
Proof.
  apply (tm_ind_strong (fun t => forall env w,
           wf_tm (length env) t = true ->
           run_checked env t w = Some (run env t w))).
  - (* Ret *)
    intros v env w H; cbn in H |- *.
    rewrite (eval_val_checked_wf env v H). reflexivity.
  - (* Bind *)
    intros t1 t2 IH1 IH2 env w H; cbn in H.
    apply andb_true_iff in H as [H1 H2].
    cbn. rewrite (IH1 env w H1).
    destruct (run env t1 w) as [[x | e] w'].
    + apply (IH2 (x :: env) w'). exact H2.
    + reflexivity.
  - (* Perform *)
    intros o args env w H; cbn in H.
    apply andb_true_iff in H as [_ Hargs].
    cbn. rewrite (eval_vals_checked_wf env args Hargs).
    reflexivity.
  - (* Match *)
    intros scrut branches default HF Hdef env w H.
    rewrite wf_tm_match_eq in H.
    apply andb_true_iff in H as [H1 Hwd];
      apply andb_true_iff in H1 as [Hs Hwb].
    rewrite run_checked_match_eq, run_match_eq.
    rewrite (eval_val_checked_wf env scrut Hs).
    apply try_branches_checked_agrees; assumption.
  - (* Repeat *)
    intros n body IHb env w H; cbn in H.
    rewrite run_checked_repeat_eq, run_repeat_eq.
    apply repeat_loop_checked_agrees; [exact IHb | exact H].
  - (* Prim *)
    intros p args env w H; cbn in H.
    apply andb_true_iff in H as [_ Hargs].
    cbn. rewrite (eval_vals_checked_wf env args Hargs).
    reflexivity.
  - (* Fold *)
    intros lst init body IHi IHb env w H; cbn in H.
    apply andb_true_iff in H as [H1 Hb];
      apply andb_true_iff in H1 as [Hl Hi].
    rewrite run_checked_fold_eq, run_fold_eq.
    rewrite (eval_val_checked_wf env lst Hl).
    rewrite (IHi env w Hi).
    destruct (run env init w) as [[acc0 | e] w'].
    + destruct (eval_val env lst); try reflexivity.
      apply fold_elems_checked_agrees; [exact IHb | exact Hb].
    + reflexivity.
Qed.

(** The never-[None] reading: a wf program's run never hits the scope marker. *)
Corollary wf_run_checked_not_none : forall t env w,
  wf_tm (length env) t = true ->
  run_checked env t w <> None.
Proof.
  intros t env w H; rewrite (wf_no_scope_stuck t env w H); discriminate.
Qed.

(** Top-level form: a closed wf program agrees with [run_top] on every context and
    instant (this is the statement the codegen gate realizes: [wf_tm 0] passed =>
    no scope-[Dstuck], ever). *)
Corollary wf_run_top_no_scope_stuck : forall t c now,
  wf_tm 0%nat t = true ->
  run_checked [] t (init_world c now) = Some (run_top c now t).
Proof.
  intros t c now H; apply (wf_no_scope_stuck t [] (init_world c now) H).
Qed.

(* ===== §8  Anti-vacuity: the ill-scoped program ============================= *)

(** [VVar 2] under ONE binder ([Bind] provides depth 1; index 2 is out of scope). *)
Definition ill_scoped : tm :=
  Bind (Ret (VInt 5)) (Ret (VVar 2)).

(** The checker rejects it... *)
Theorem wf_rejects_ill_scoped : wf_tm 0%nat ill_scoped = false.
Proof. vm_compute. reflexivity. Qed.

(** ... its run REALLY hits the scope [Dstuck] (the failure class the theorem kills)... *)
Theorem ill_scoped_hits_dstuck :
  fst (run_top DUnit 0 ill_scoped) = ORet Dstuck.
Proof. vm_compute. reflexivity. Qed.

(** ... and the instrumented run hits the [None] marker on it — the marker genuinely
    fires on non-wf input, so [wf_no_scope_stuck] is not vacuously about a marker that
    never triggers. *)
Theorem ill_scoped_checked_none :
  run_checked [] ill_scoped (init_world DUnit 0) = None.
Proof. vm_compute. reflexivity. Qed.

(* ===== §9  Anti-vacuity: the Fold-clause mutant checker ===================== *)

(** MUTANT (adr-0014 §3): a local copy of [wf_tm] whose [Fold] clause SKIPS the
    (+2)-extended body check entirely. NB the mutation direction: any depth-REDUCING
    variant (e.g. checking the body at [depth] instead of [S (S depth)]) accepts a
    SUBSET of the reference-accepted programs — [wf_val]/[wf_tm] are monotone in
    [depth] — so it can never accept a stuck program; it is caught by INHABITANCE
    instead (§10, [mutant_noext_rejects_real_program]). The laxer skip below is the
    mutation the soundness statement itself must reject. EffIR is untouched — the
    TimeStore.v/Fold.v/Journal.v local-mutant technique. *)
Fixpoint wf_tm_mutant (depth : nat) (t : tm) : bool :=
  match t with
  | Ret v          => wf_val depth v
  | Bind t1 t2     => wf_tm_mutant depth t1 && wf_tm_mutant (S depth) t2
  | Perform o args =>
      Nat.eqb (length args) (op_arity o) && forallb (wf_val depth) args
  | Match scrut branches default =>
      wf_val depth scrut
      && (fix wf_bs (bs : list (pat * tm)) : bool :=
            match bs with
            | []                => true
            | (p, body) :: rest =>
                wf_tm_mutant (pat_binders p + depth)%nat body && wf_bs rest
            end) branches
      && wf_tm_mutant depth default
  | Repeat _ body  => wf_tm_mutant depth body
  | Prim p args    =>
      Nat.eqb (length args) (prim_arity p) && forallb (wf_val depth) args
  | Fold lst init body =>
      wf_val depth lst && wf_tm_mutant depth init   (* MUTANT: body (+2) check SKIPPED *)
  end.

(** The probe: a Fold whose body references [VVar 5] — the body env has length 2
    (element + accumulator), so the run evaluates an out-of-scope var. The correct
    twin returns the element ([VVar 1], legal at body depth 2). *)
Definition fold_bad : tm :=
  Fold (VList [VInt 7]) (Ret VUnit) (Ret (VVar 5)).

Definition fold_good : tm :=
  Fold (VList [VInt 7]) (Ret VUnit) (Ret (VVar 1)).

(** The mutant ACCEPTS the bad program... *)
Theorem mutant_accepts_fold_bad : wf_tm_mutant 0%nat fold_bad = true.
Proof. vm_compute. reflexivity. Qed.

(** ... the REAL checker rejects it... *)
Theorem wf_rejects_fold_bad : wf_tm 0%nat fold_bad = false.
Proof. vm_compute. reflexivity. Qed.

(** ... and the bad program's run demonstrably produces [Dstuck]-tainted output
    (the fold's final accumulator IS the scope-stuck sentinel)... *)
Theorem fold_bad_output_dstuck :
  fst (run_top DUnit 0 fold_bad) = ORet Dstuck.
Proof. vm_compute. reflexivity. Qed.

(** ... observably different from the correct twin (which yields the element). *)
Theorem fold_bad_observably_differs :
  fst (run_top DUnit 0 fold_bad) <> fst (run_top DUnit 0 fold_good).
Proof. vm_compute. intro H. discriminate H. Qed.

(** The correct twin is wf, so the pair is a genuine accept/reject boundary. *)
Theorem fold_good_wf : wf_tm 0%nat fold_good = true.
Proof. vm_compute. reflexivity. Qed.

(* ===== §10  Inhabitance ===================================================== *)

(** The checker accepts EVERY program of the single-source list — [wf_tm] is not a
    universal rejector, and the codegen gate (adr-0014 §4) keeps this true in CI
    forever (the extracted [wf_tm] runs on [all_programs] before every emission). *)
Theorem wf_all_programs :
  forallb (fun nt => wf_tm 0%nat (snd nt)) all_programs = true.
Proof. vm_compute. reflexivity. Qed.

(** The OTHER mutation direction (skipping the extension by checking the [Fold] body
    at the UNextended depth) is strictly stricter — it cannot accept a stuck program,
    but it breaks inhabitance: it rejects the real R6 sample whose body uses the
    element/accumulator binders. This is what the [wf_all_programs] gate catches. *)
Fixpoint wf_tm_mutant_noext (depth : nat) (t : tm) : bool :=
  match t with
  | Ret v          => wf_val depth v
  | Bind t1 t2     => wf_tm_mutant_noext depth t1 && wf_tm_mutant_noext (S depth) t2
  | Perform o args =>
      Nat.eqb (length args) (op_arity o) && forallb (wf_val depth) args
  | Match scrut branches default =>
      wf_val depth scrut
      && (fix wf_bs (bs : list (pat * tm)) : bool :=
            match bs with
            | []                => true
            | (p, body) :: rest =>
                wf_tm_mutant_noext (pat_binders p + depth)%nat body && wf_bs rest
            end) branches
      && wf_tm_mutant_noext depth default
  | Repeat _ body  => wf_tm_mutant_noext depth body
  | Prim p args    =>
      Nat.eqb (length args) (prim_arity p) && forallb (wf_val depth) args
  | Fold lst init body =>
      wf_val depth lst && wf_tm_mutant_noext depth init
      && wf_tm_mutant_noext depth body              (* MUTANT: no (+2) extension *)
  end.

Theorem mutant_noext_rejects_real_program :
  wf_tm_mutant_noext 0%nat sample_fold_trace = false.
Proof. vm_compute. reflexivity. Qed.

Theorem wf_accepts_sample_fold_trace :
  wf_tm 0%nat sample_fold_trace = true.
Proof. vm_compute. reflexivity. Qed.

(** Explicit-witness inhabitance of the theorem's precondition: a wf program exists
    (prog0), and on it [run_checked] is genuinely [Some] of the reference run. *)
Lemma wf_precondition_inhabited :
  exists t, wf_tm 0%nat t = true
    /\ run_checked [] t (init_world DUnit 0) = Some (run_top DUnit 0 prog0).
Proof.
  exists prog0. split; vm_compute; reflexivity.
Qed.

(* ===== §11  Print Assumptions =============================================== *)

(** Each must read "Closed under the global context". *)
Print Assumptions wf_tm_match_eq.
Print Assumptions eval_val_checked_wf.
Print Assumptions eval_val_checked_total.
Print Assumptions eval_vals_checked_wf.
Print Assumptions push_env_length.
Print Assumptions match_pat_binders.
Print Assumptions try_branches_checked_agrees.
Print Assumptions repeat_loop_checked_agrees.
Print Assumptions fold_elems_checked_agrees.
Print Assumptions wf_no_scope_stuck.
Print Assumptions wf_run_checked_not_none.
Print Assumptions wf_run_top_no_scope_stuck.
Print Assumptions wf_rejects_ill_scoped.
Print Assumptions ill_scoped_hits_dstuck.
Print Assumptions ill_scoped_checked_none.
Print Assumptions mutant_accepts_fold_bad.
Print Assumptions wf_rejects_fold_bad.
Print Assumptions fold_bad_output_dstuck.
Print Assumptions fold_bad_observably_differs.
Print Assumptions fold_good_wf.
Print Assumptions wf_all_programs.
Print Assumptions mutant_noext_rejects_real_program.
Print Assumptions wf_accepts_sample_fold_trace.
Print Assumptions wf_precondition_inhabited.
