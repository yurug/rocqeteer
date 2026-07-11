(** * TimeStore — R4+R5 theorem set for the Time effect and the expiring store
    (adr-0011-time-and-expiring-store).

    Every theorem below is fully proved by vm_compute on a CLOSED run (no unproved proof
    obligations, no axioms); Print Assumptions must read "Closed under the global context"
    for each.

    Contents:
    1. Store laws over programs: get-after-put (same/other key), put CLEARS the deadline,
       set-then-get deadline, set-deadline-on-missing = false, delete returns liveness.
    2. THE BOUNDARY (the load-bearing rule, oracle-validated: 12,500-case
       prediction-vs-oracle run, 0 mismatches): a binding with deadline [d] is ALIVE at
       [now = d] and DEAD at [now = d+1] — for OGet, OGetDeadline, ODelete, and [observe].
    3. ONow flows: the run instant reaches programs and combines with prims
       (deadline arithmetic now+1000 via PAddChecked) at concrete instants incl. 0 and a
       negative now; overflow near int64_max takes the DNone path.
    4. MUTANT (anti-vacuity): a copy of the semantics whose liveness uses [<] (dead AT
       the deadline) — defined locally, EffIR untouched — is OBSERVABLY different on a
       concrete program at [now = d], so the boundary statements genuinely reject it.
    5. Inhabitance for a deadline-carrying store state (explicit witness — see the
       theories/Prims.v header note on vm_compute and open existentials). *)

From Stdlib Require Import ZArith List String Ascii.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

(* ===== §1  Store laws ====================================================== *)

Definition ka : list ascii := list_ascii_of_string "a".
Definition kb : list ascii := list_ascii_of_string "b".

(** put "a" := 42; get "a"  ->  DSome 42 (live, deadline-less). *)
Theorem get_put_same_live :
  let '(o, _) := run_top DUnit 0 (Bind (Perform OPut [VBytes ka; VInt 42])
                                       (Perform OGet [VBytes ka])) in
  o = ORet (DSome (DInt 42)).
Proof. vm_compute. reflexivity. Qed.

(** put "a" := 42; get "b"  ->  DNone (another key is untouched). *)
Theorem get_put_other_key :
  let '(o, _) := run_top DUnit 0 (Bind (Perform OPut [VBytes ka; VInt 42])
                                       (Perform OGet [VBytes kb])) in
  o = ORet DNone.
Proof. vm_compute. reflexivity. Qed.

(** OPut CLEARS the deadline: [sample_put_clears] = put; set deadline 500; put again;
    get_deadline. Result is DSome DNone (live binding, NO deadline) — both while the
    intermediate deadline is still live (now = 0)... *)
Theorem put_clears_deadline :
  let '(o, _) := run_top DUnit 0 sample_put_clears in
  o = ORet (DSome DNone).
Proof. vm_compute. reflexivity. Qed.

(** ... and after it would have expired (now = 501): the second put replaces the expired
    binding wholesale, so the observable is identical. *)
Theorem put_clears_deadline_past_expiry :
  let '(o, _) := run_top DUnit 501 sample_put_clears in
  o = ORet (DSome DNone).
Proof. vm_compute. reflexivity. Qed.

(** set-then-get deadline: [sample_ttl] at now = 0 reads back the deadline it set —
    OGetDeadline's nested-option encoding: DSome (DSome (DInt 1000)). *)
Theorem setdeadline_then_getdeadline :
  let '(o, _) := run_top DUnit 0 sample_ttl in
  o = ORet (DPair (DSome (DInt 7)) (DPair (DSome (DSome (DInt 1000))) (DBool true))).
Proof. vm_compute. reflexivity. Qed.

(** OSetDeadline on a missing key modifies nothing and returns DBool false. *)
Theorem setdeadline_missing_key_false :
  let '(o, w) := run_top DUnit 0 sample_setdl_missing in
  o = ORet (DBool false) /\ M.elements w.(kv) = [].
Proof. vm_compute. split; reflexivity. Qed.

(** ODelete returns DBool true iff a LIVE binding was removed: [sample_store] deletes a
    live deadline-less binding (true) and the following get sees it gone (DNone). *)
Theorem delete_live_true :
  let '(o, _) := run_top DUnit 0 sample_store in
  o = ORet (DPair (DSome (DInt 41)) (DPair (DBool true) DNone)).
Proof. vm_compute. reflexivity. Qed.

(** ODelete on an EXPIRED binding returns DBool false (expired = semantically absent):
    deadline 500, deleted at now = 1000. *)
Theorem delete_expired_false :
  let '(o, _) := run_top DUnit 1000
    (Bind (Perform OPut [VBytes ka; VInt 1])
    (Bind (Perform OSetDeadline [VBytes ka; VSome (VInt 500)])
          (Perform ODelete [VBytes ka]))) in
  o = ORet (DBool false).
Proof. vm_compute. reflexivity. Qed.

(** OSetDeadline VNone (persist) on a live binding clears the deadline (true, then
    DSome DNone)... *)
Theorem persist_clears_deadline :
  let '(o, _) := run_top DUnit 0 sample_persist in
  o = ORet (DPair (DBool true) (DSome DNone)).
Proof. vm_compute. reflexivity. Qed.

(** ... but on an ALREADY-EXPIRED binding it modifies nothing (false, still absent). *)
Theorem persist_after_expiry_false :
  let '(o, _) := run_top DUnit 801 sample_persist in
  o = ORet (DPair (DBool false) DNone).
Proof. vm_compute. reflexivity. Qed.

(* ===== §2  THE BOUNDARY: live iff now <= d ================================= *)

(** ALIVE AT THE DEADLINE (now = d = 1000): OGet returns the value AND OGetDeadline shows
    the deadline AND ODelete removes a live binding. Oracle-validated boundary — the [<]
    mutant below fails exactly here. *)
Theorem alive_at_deadline :
  let '(o, _) := run_top DUnit 1000 sample_ttl in
  o = ORet (DPair (DSome (DInt 7)) (DPair (DSome (DSome (DInt 1000))) (DBool true))).
Proof. vm_compute. reflexivity. Qed.

(** DEAD STRICTLY PAST THE DEADLINE (now = d+1 = 1001): OGet DNone, OGetDeadline DNone,
    ODelete DBool false. *)
Theorem dead_past_deadline :
  let '(o, _) := run_top DUnit 1001 sample_ttl in
  o = ORet (DPair DNone (DPair DNone (DBool false))).
Proof. vm_compute. reflexivity. Qed.

(** [observe] filters by the run's instant: a binding with deadline 500 is ABSENT from
    the observable at now = 501, while its deadline-less neighbour survives. *)
Definition obs_prog : tm :=
  Bind (Perform OPut [VBytes ka; VInt 1])
  (Bind (Perform OSetDeadline [VBytes ka; VSome (VInt 500)])
        (Perform OPut [VBytes kb; VInt 2])).

Theorem expired_absent_from_observe :
  observe DUnit 501 obs_prog
  = (ORet DUnit, [("b"%string, (DInt 2, None))], []).
Proof. vm_compute. reflexivity. Qed.

(** Companion (anti-vacuity for the filter): at the exact deadline (now = 500) the same
    binding IS in the observable, deadline included — the filter is live-driven, not a
    blanket drop of deadline-carrying entries. *)
Theorem live_at_deadline_in_observe :
  observe DUnit 500 obs_prog
  = (ORet DUnit,
     [("a"%string, (DInt 1, Some 500)); ("b"%string, (DInt 2, None))], []).
Proof. vm_compute. reflexivity. Qed.

(* ===== §3  ONow flows ====================================================== *)

(** The bare Time op: ONow returns the run's instant. *)
Theorem now_returns :
  let '(o, _) := run_top DUnit 42 (Perform ONow []) in
  o = ORet (DInt 42).
Proof. vm_compute. reflexivity. Qed.

(** Deadline arithmetic via prims ([sample_now] = ONow; PAddChecked now 1000): the
    instant flows into the program and combines with the checked add — at now = 0... *)
Theorem now_flows_zero :
  let '(o, _) := run_top DUnit 0 sample_now in
  o = ORet (DPair (DInt 0) (DInt 1000)).
Proof. vm_compute. reflexivity. Qed.

(** ... at a NEGATIVE instant (clocks before the epoch are still one total order)... *)
Theorem now_flows_negative :
  let '(o, _) := run_top DUnit (-5000) sample_now in
  o = ORet (DPair (DInt (-5000)) (DInt (-4000))).
Proof. vm_compute. reflexivity. Qed.

(** ... and at int64_max the checked add overflows, taking the DNone default arm. *)
Theorem now_flows_overflow :
  let '(o, _) := run_top DUnit int64_max sample_now in
  o = ORet DNone.
Proof. vm_compute. reflexivity. Qed.

(* ===== §4  MUTANT: liveness with < (dead AT the deadline) ================== *)

(** The mutant liveness helper — the ONLY change is [<?] for [<=?]. Defined locally
    (EffIR untouched), same technique as StructVal.v's swapped-tags mutant. *)
Definition live_mut (now : Z) (e : entry) : bool :=
  match snd e with
  | None   => true
  | Some d => now <? d      (* MUTANT: strictly-less — dead AT the deadline *)
  end.

Definition find_live_mut (now : Z) (k : string) (s : state) : option entry :=
  match M.find k s with
  | Some e => if live_mut now e then Some e else None
  | None   => None
  end.

(** Mutant store handler: verbatim [handle_store] with [find_live_mut]. *)
Definition handle_store_mut (now : Z) (o : op) (args : list dval) (s : state)
  : dval * state :=
  match o, args with
  | OGet, [DBytes kbs] =>
      (match find_live_mut now (string_of_list_ascii kbs) s with
       | Some (v, _) => DSome v
       | None        => DNone
       end, s)
  | OPut, [DBytes kbs; v] =>
      (DUnit, M.add (string_of_list_ascii kbs) (v, None) s)
  | ODelete, [DBytes kbs] =>
      let k := string_of_list_ascii kbs in
      (match find_live_mut now k s with
       | Some _ => DBool true
       | None   => DBool false
       end, M.remove k s)
  | OGetDeadline, [DBytes kbs] =>
      (match find_live_mut now (string_of_list_ascii kbs) s with
       | Some (_, None)   => DSome DNone
       | Some (_, Some d) => DSome (DSome (DInt d))
       | None             => DNone
       end, s)
  | OSetDeadline, [DBytes kbs; DNone] =>
      let k := string_of_list_ascii kbs in
      match find_live_mut now k s with
      | Some (v, _) => (DBool true, M.add k (v, None) s)
      | None        => (DBool false, s)
      end
  | OSetDeadline, [DBytes kbs; DSome (DInt d)] =>
      let k := string_of_list_ascii kbs in
      match find_live_mut now k s with
      | Some (v, _) => (DBool true, M.add k (v, Some d) s)
      | None        => (DBool false, s)
      end
  | _, _ => (Dstuck, s)
  end.

(** Mutant interpreter: verbatim [run] with [handle_store_mut] at the store dispatch. *)
Fixpoint run_mut (env : list dval) (t : tm) (w : world) : outcome * world :=
  match t with
  | Ret v        => (ORet (eval_val env v), w)
  | Bind t1 t2   =>
      match run_mut env t1 w with
      | (ORet x, w') => run_mut (x :: env) t2 w'
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
                     | [DBytes kbs] =>
                         (ORet (opt_to_dval (M.find (string_of_list_ascii kbs) w.(cache))), w)
                     | _        => (ORet Dstuck, w)
                     end
      | OCachePut => match vs with
                     | [DBytes kbs; v] =>
                         (ORet DUnit, set_cache w (M.add (string_of_list_ascii kbs) v w.(cache)))
                     | _           => (ORet Dstuck, w)
                     end
      | _      => let '(r, s') := handle_store_mut w.(now_ms) o vs w.(kv) in
                  (ORet r, set_kv w s')
      end
  | Match scrut branches default =>
      let d := eval_val env scrut in
      (fix try_branches (bs : list (pat * tm)) {struct bs} : outcome * world :=
         match bs with
         | []           => run_mut env default w
         | (p, body) :: rest =>
             match match_pat p d with
             | Some payloads => run_mut (push_env payloads env) body w
             | None => try_branches rest
             end
         end) branches
  | Repeat n body =>
      (fix loop (m : nat) (w0 : world) {struct m} : outcome * world :=
         match m with
         | O    => (ORet DUnit, w0)
         | S m' => match run_mut env body w0 with
                   | (ORet _, w1) => loop m' w1
                   | (OErr e, w1) => (OErr e, w1)
                   end
         end) n w
  | Prim p args =>
      let vs := map (eval_val env) args in
      (ORet (apply_prim p vs), w)
  end.

Definition run_top_mut (c : dval) (now : Z) (t : tm) : outcome * world :=
  run_mut [] t (init_world c now).

(** Under the mutant, the SAME program at the SAME instant (now = d = 1000) sees the
    binding DEAD at its deadline: get DNone, get_deadline DNone, delete false. *)
Theorem mutant_dead_at_deadline :
  let '(o, _) := run_top_mut DUnit 1000 sample_ttl in
  o = ORet (DPair DNone (DPair DNone (DBool false))).
Proof. vm_compute. reflexivity. Qed.

(** Therefore the mutant is OBSERVABLY DIFFERENT from the reference semantics on a
    concrete program at the boundary — [alive_at_deadline] genuinely rejects the [<]
    liveness rule (adr-0011 §implementers: anti-vacuity for the boundary). *)
Theorem mutant_observably_differs :
  (let '(o, _) := run_top DUnit 1000 sample_ttl in o)
  <>
  (let '(o, _) := run_top_mut DUnit 1000 sample_ttl in o).
Proof. vm_compute. intro H. discriminate H. Qed.

(* ===== §5  Inhabitance for a deadline-carrying state ======================= *)

(** A store state carrying a live deadline exists and is live AT its deadline — explicit
    witness, vm_compute only on closed conjuncts (theories/Prims.v header note). *)
Lemma deadline_state_inhabited :
  exists (s : state),
    M.find ("a"%string) s = Some (DInt 7, Some 1000)
    /\ find_live 1000 ("a"%string) s = Some (DInt 7, Some 1000)
    /\ find_live 1001 ("a"%string) s = None.
Proof.
  exists (M.add ("a"%string) (DInt 7, Some 1000) (M.empty entry)).
  split; [ vm_compute; reflexivity | split; vm_compute; reflexivity ].
Qed.

(** Print Assumptions footprint — each must say "Closed under the global context". *)
Print Assumptions get_put_same_live.
Print Assumptions get_put_other_key.
Print Assumptions put_clears_deadline.
Print Assumptions put_clears_deadline_past_expiry.
Print Assumptions setdeadline_then_getdeadline.
Print Assumptions setdeadline_missing_key_false.
Print Assumptions delete_live_true.
Print Assumptions delete_expired_false.
Print Assumptions persist_clears_deadline.
Print Assumptions persist_after_expiry_false.
Print Assumptions alive_at_deadline.
Print Assumptions dead_past_deadline.
Print Assumptions expired_absent_from_observe.
Print Assumptions live_at_deadline_in_observe.
Print Assumptions now_returns.
Print Assumptions now_flows_zero.
Print Assumptions now_flows_negative.
Print Assumptions now_flows_overflow.
Print Assumptions mutant_dead_at_deadline.
Print Assumptions mutant_observably_differs.
Print Assumptions deadline_state_inhabited.
