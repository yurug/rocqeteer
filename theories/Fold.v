(** * Fold — R6 theorem set for list elimination (adr-0012-list-elimination),
    plus the R8 CONFIRMATION theorems (error payloads).

    Every theorem is fully proved by vm_compute on a CLOSED run; Print Assumptions must
    read "Closed under the global context" for each. Witnesses are EXPLICIT, never
    [eexists] followed by a multi-goal vm_compute (theories/Prims.v header note).

    Contents:
    1. End-to-end effectful fold: [sample_fold_put] over a concrete MIXED DList — each
       element Put at its iteration-index key, counter stepped via PAddChecked; final
       accumulator AND final store pinned.
    2. ORDER observability: a list and its reverse give different observables, both via
       a non-commutative accumulator (PBytesConcat) and via the trace; a local
       fold-RIGHT mutant interpreter is proven observably different (anti-vacuity).
    3. Error short-circuit: body throws on element k -> OErr with exactly the pre-k puts
       in the final store; an aborting [init] never starts the fold.
    4. Non-DList scrutinee -> the fold is EMPTY: result = init's result, init's effects
       happen exactly once (documented posture, adr-0012 §Decision 2 — R10 will reject
       such programs statically).
    5. Empty list / singleton; accumulator-overflow path through PAddChecked.
    6. PListLen / PListNth boundary lemmas (i = -1, 0, len-1, len; empty list; huge
       index beyond native int; shape mismatches) and PMulChecked boundaries
       (int64_max * 2; the asymmetric -1 * int64_min = 2^63 overflow; seconds->ms
       scaling 1000 * s in range).
    7. R8 CONFIRMATION: error values carry ARBITRARY dvals — including exact byte-string
       messages and DTag-structured payloads — and have since R1/M1 ([OThrow] takes any
       val, [OErr e] carries any dval; nothing restricts e to DInt). The theorems below
       pin the OErr payload bytes EXACTLY, making the capability deliberate rather than
       incidental. No new machinery — R8 closes here.
    8. Inhabitance (explicit witnesses) + the Print Assumptions block. *)

From Stdlib Require Import ZArith List String Ascii.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

(* ===== §1  End-to-end effectful fold over a mixed list ===================== *)

(** The concrete MIXED list: shapes DInt / DBytes / DInt. *)
Definition mixed_ctx : dval :=
  DList [DInt 5; DBytes (list_ascii_of_string "x"); DInt 7].

(** [sample_fold_put] over the mixed list: final accumulator = element count (DInt 3),
    final store = each element at its iteration-index key ("0", "1", "2"), no trace.
    This is the load-bearing end-to-end theorem: OPut per element (world threads through
    iterations) + the PAddChecked counter (prims compose with Fold). *)
Theorem fold_mixed_end_to_end :
  observe mixed_ctx 0 sample_fold_put
  = (ORet (DInt 3),
     [("0"%string, (DInt 5, None));
      ("1"%string, (DBytes (list_ascii_of_string "x"), None));
      ("2"%string, (DInt 7, None))],
     []).
Proof. vm_compute. reflexivity. Qed.

(* ===== §2  ORDER observability ============================================= *)

(** Non-commutative accumulator: [sample_fold_concat] concatenates acc ++ elem left to
    right, so ["A"; "BC"] yields "ABC"... *)
Definition concat_ctx_fwd : dval :=
  DList [DBytes (list_ascii_of_string "A"); DBytes (list_ascii_of_string "BC")].
Definition concat_ctx_rev : dval :=
  DList [DBytes (list_ascii_of_string "BC"); DBytes (list_ascii_of_string "A")].

Theorem fold_concat_forward :
  let '(o, _) := run_top concat_ctx_fwd 0 sample_fold_concat in
  o = ORet (DBytes (list_ascii_of_string "ABC")).
Proof. vm_compute. reflexivity. Qed.

(** ... while the REVERSED list yields "BCA" — the element order is observable in the
    accumulator. *)
Theorem fold_concat_reversed :
  let '(o, _) := run_top concat_ctx_rev 0 sample_fold_concat in
  o = ORet (DBytes (list_ascii_of_string "BCA")).
Proof. vm_compute. reflexivity. Qed.

Theorem fold_concat_order_observable :
  (let '(o, _) := run_top concat_ctx_fwd 0 sample_fold_concat in o)
  <>
  (let '(o, _) := run_top concat_ctx_rev 0 sample_fold_concat in o).
Proof. vm_compute. intro H. discriminate H. Qed.

(** The trace shows the same order: [sample_fold_trace] emits each element left to
    right, so the chronological trace IS the input list... *)
Definition trace_ctx_fwd : dval := DList [DInt 1; DInt 2; DInt 3].
Definition trace_ctx_rev : dval := DList [DInt 3; DInt 2; DInt 1].

Theorem fold_trace_forward :
  observe trace_ctx_fwd 0 sample_fold_trace
  = (ORet DUnit, [], [DInt 1; DInt 2; DInt 3]).
Proof. vm_compute. reflexivity. Qed.

Theorem fold_trace_reversed :
  observe trace_ctx_rev 0 sample_fold_trace
  = (ORet DUnit, [], [DInt 3; DInt 2; DInt 1]).
Proof. vm_compute. reflexivity. Qed.

Theorem fold_trace_order_observable :
  observe trace_ctx_fwd 0 sample_fold_trace <> observe trace_ctx_rev 0 sample_fold_trace.
Proof. vm_compute. intro H. discriminate H. Qed.

(* ===== §2b  MUTANT: a fold-RIGHT interpreter =============================== *)

(** The mutant interpreter — verbatim [run], except the [Fold] case iterates the
    REVERSED element list (i.e. a right fold with the same accumulator body). Defined
    locally, EffIR untouched — the TimeStore.v / StructVal.v mutant technique. *)
Fixpoint run_foldr (env : list dval) (t : tm) (w : world) : outcome * world :=
  match t with
  | Ret v        => (ORet (eval_val env v), w)
  | Bind t1 t2   =>
      match run_foldr env t1 w with
      | (ORet x, w') => run_foldr (x :: env) t2 w'
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
      | _      => let '(r, s') := handle_store w.(now_ms) o vs w.(kv) in (ORet r, set_kv w s')
      end
  | Match scrut branches default =>
      let d := eval_val env scrut in
      (fix try_branches (bs : list (pat * tm)) {struct bs} : outcome * world :=
         match bs with
         | []           => run_foldr env default w
         | (p, body) :: rest =>
             match match_pat p d with
             | Some payloads => run_foldr (push_env payloads env) body w
             | None => try_branches rest
             end
         end) branches
  | Repeat n body =>
      (fix loop (m : nat) (w0 : world) {struct m} : outcome * world :=
         match m with
         | O    => (ORet DUnit, w0)
         | S m' => match run_foldr env body w0 with
                   | (ORet _, w1) => loop m' w1
                   | (OErr e, w1) => (OErr e, w1)
                   end
         end) n w
  | Prim p args =>
      let vs := map (eval_val env) args in
      (ORet (apply_prim p vs), w)
  | Fold lst init body =>
      let d := eval_val env lst in
      match run_foldr env init w with
      | (OErr e, w') => (OErr e, w')
      | (ORet acc0, w') =>
          match d with
          | DList vs =>
              (fix fold_elems (xs : list dval) (acc : dval) (w0 : world) {struct xs}
                 : outcome * world :=
                 match xs with
                 | []       => (ORet acc, w0)
                 | x :: xs' =>
                     match run_foldr (push_env [x; acc] env) body w0 with
                     | (ORet acc', w1) => fold_elems xs' acc' w1
                     | (OErr e, w1)    => (OErr e, w1)
                     end
                 end) (List.rev vs) acc0 w'   (* MUTANT: right fold — reversed order *)
          | _ => (ORet acc0, w')
          end
      end
  end.

Definition run_top_foldr (c : dval) (now : Z) (t : tm) : outcome * world :=
  run_foldr [] t (init_world c now).

(** Under the mutant, the SAME program on the SAME list concatenates right-to-left:
    ["A"; "BC"] yields "BCA" instead of "ABC". *)
Theorem mutant_foldr_concat :
  let '(o, _) := run_top_foldr concat_ctx_fwd 0 sample_fold_concat in
  o = ORet (DBytes (list_ascii_of_string "BCA")).
Proof. vm_compute. reflexivity. Qed.

(** Therefore the fold-RIGHT mutant is OBSERVABLY different from the reference left
    fold on a concrete program — [fold_concat_forward] genuinely pins the direction
    (adr-0012 §implementers: anti-vacuity for the order). *)
Theorem mutant_foldr_observably_differs :
  (let '(o, _) := run_top concat_ctx_fwd 0 sample_fold_concat in o)
  <>
  (let '(o, _) := run_top_foldr concat_ctx_fwd 0 sample_fold_concat in o).
Proof. vm_compute. intro H. discriminate H. Qed.

(* ===== §3  Error short-circuit ============================================= *)

(** Body throws on element k = 1 (0-based; the poison "BAD"): the outcome is OErr with
    the poison payload, and the store shows EXACTLY the puts of the elements BEFORE the
    poison — element 0 was Put, element 2 was never reached. *)
Definition guard_ctx : dval :=
  DList [DInt 1; DBytes poison_bytes; DInt 2].

Theorem fold_guard_short_circuit :
  observe guard_ctx 0 sample_fold_guard
  = (OErr (DBytes poison_bytes), [("0"%string, (DInt 1, None))], []).
Proof. vm_compute. reflexivity. Qed.

(** Poison FIRST: zero puts are visible (k = 0 prior effects = none). *)
Theorem fold_guard_poison_first :
  observe (DList [DBytes poison_bytes; DInt 1]) 0 sample_fold_guard
  = (OErr (DBytes poison_bytes), [], []).
Proof. vm_compute. reflexivity. Qed.

(** An aborting [init] short-circuits the whole Fold: the elements are never visited
    (no puts), and the outcome is init's error. Local program — Fold with a throwing
    init over a non-empty list. *)
Definition fold_init_throws : tm :=
  Fold (VList [VInt 1; VInt 2]) (Perform OThrow [VInt 9]) fold_put_body.

Theorem fold_init_throw_short_circuits :
  observe DUnit 0 fold_init_throws = (OErr (DInt 9), [], []).
Proof. vm_compute. reflexivity. Qed.

(* ===== §4  Non-DList scrutinee: the fold is EMPTY ========================== *)

(** DOCUMENTED POSTURE (adr-0012 §Decision 2): a non-DList scrutinee makes the fold
    empty — the result is init's result, no body iteration runs, no error is raised.
    Total without a typechecker (same posture as prim shape mismatch); the R10
    typechecker will reject such programs statically. *)
Theorem fold_non_list_yields_init :
  observe (DInt 3) 0 sample_fold_put = (ORet (DInt 0), [], []).
Proof. vm_compute. reflexivity. Qed.

(** Init's EFFECTS still happen exactly once on a non-list scrutinee — "run init only"
    is run, not skip: the init put is in the final store; the body put never runs. *)
Definition fold_effectful_init : tm :=
  Fold (VInt 7)
       (Bind (Perform OPut [VBytes key1; VInt 5]) (Ret (VInt 0)))
       fold_put_body.

Theorem fold_non_list_runs_init_effects :
  observe DUnit 0 fold_effectful_init
  = (ORet (DInt 0), [("1"%string, (DInt 5, None))], []).
Proof. vm_compute. reflexivity. Qed.

(* ===== §5  Empty list / singleton / accumulator overflow =================== *)

Theorem fold_empty_list_yields_init :
  observe (DList []) 0 sample_fold_put = (ORet (DInt 0), [], []).
Proof. vm_compute. reflexivity. Qed.

Theorem fold_singleton :
  observe (DList [DInt 42]) 0 sample_fold_put
  = (ORet (DInt 1), [("0"%string, (DInt 42, None))], []).
Proof. vm_compute. reflexivity. Qed.

(** Accumulator overflow through the PAddChecked path: [sample_fold_ovf] starts the
    counter at int64_max, so the FIRST element is Put (at key "9223372036854775807"),
    then the counter step overflows -> DNone -> the body throws ovf_bytes. The pre-abort
    put is committed — exactly the Bind/OErr discipline inside a Fold body. *)
Theorem fold_acc_overflow :
  observe (DList [DInt 5]) 0 sample_fold_ovf
  = (OErr (DBytes ovf_bytes),
     [("9223372036854775807"%string, (DInt 5, None))], []).
Proof. vm_compute. reflexivity. Qed.

(** Empty list on the overflow sample: the fold is empty, the max-valued init survives. *)
Theorem fold_ovf_empty_list :
  let '(o, _) := run_top (DList []) 0 sample_fold_ovf in
  o = ORet (DInt int64_max).
Proof. vm_compute. reflexivity. Qed.

(* ===== §6  PListLen / PListNth / PMulChecked boundaries ==================== *)

Definition l3 : list dval := [DInt 10; DBytes (list_ascii_of_string "y"); DUnit].

(** PListLen: length of a mixed 3-list; empty list; shape/arity mismatches. *)
Theorem list_len_three :
  apply_prim PListLen [DList l3] = DInt 3.
Proof. vm_compute. reflexivity. Qed.

Theorem list_len_empty :
  apply_prim PListLen [DList []] = DInt 0.
Proof. vm_compute. reflexivity. Qed.

Theorem list_len_mismatch_shape :
  apply_prim PListLen [DInt 3] = DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem list_len_mismatch_arity :
  apply_prim PListLen [DList l3; DInt 0] = DNone.
Proof. vm_compute. reflexivity. Qed.

(** PListNth boundaries: i = -1 / 0 / len-1 / len (adr-0012 §implementers). *)
Theorem list_nth_neg_one :
  apply_prim PListNth [DList l3; DInt (-1)] = DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem list_nth_zero :
  apply_prim PListNth [DList l3; DInt 0] = DSome (DInt 10).
Proof. vm_compute. reflexivity. Qed.

Theorem list_nth_len_minus_one :
  apply_prim PListNth [DList l3; DInt 2] = DSome DUnit.
Proof. vm_compute. reflexivity. Qed.

Theorem list_nth_len :
  apply_prim PListNth [DList l3; DInt 3] = DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem list_nth_empty :
  apply_prim PListNth [DList []; DInt 0] = DNone.
Proof. vm_compute. reflexivity. Qed.

(** A HUGE index (2^70, beyond any native int) is rejected by the Z bound check —
    this is the reference twin of the realizer's check-in-Z-before-conversion rule
    (the prim_bytes_sub Z.Overflow lesson, runtime/prims.ml). *)
Theorem list_nth_huge_index :
  apply_prim PListNth [DList l3; DInt 1180591620717411303424] = DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem list_nth_mismatch_index :
  apply_prim PListNth [DList l3; DBytes (list_ascii_of_string "0")] = DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem list_nth_mismatch_list :
  apply_prim PListNth [DInt 0; DInt 0] = DNone.
Proof. vm_compute. reflexivity. Qed.

(** PMulChecked boundaries. int64_max * 2 overflows... *)
Theorem mul_checked_max_times_two :
  apply_prim PMulChecked [DInt int64_max; DInt 2] = DNone.
Proof. vm_compute. reflexivity. Qed.

(** ... and the ASYMMETRIC boundary: -1 * int64_min = 2^63 = int64_max + 1 -> DNone
    (the two's-complement trap a naive |a*b| <= max check would miss). *)
Theorem mul_checked_neg_one_times_min :
  apply_prim PMulChecked [DInt (-1); DInt int64_min] = DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem mul_checked_min_times_neg_one :
  apply_prim PMulChecked [DInt int64_min; DInt (-1)] = DNone.
Proof. vm_compute. reflexivity. Qed.

(** The exact boundaries themselves survive multiplication by 1. *)
Theorem mul_checked_max_times_one :
  apply_prim PMulChecked [DInt int64_max; DInt 1] = DSome (DInt int64_max).
Proof. vm_compute. reflexivity. Qed.

Theorem mul_checked_min_times_one :
  apply_prim PMulChecked [DInt int64_min; DInt 1] = DSome (DInt int64_min).
Proof. vm_compute. reflexivity. Qed.

(** The driving use case (seconds -> ms): 1000 * s for an in-range s round-trips. *)
Theorem mul_checked_seconds_to_ms :
  apply_prim PMulChecked [DInt 1000; DInt 9007199254740] = DSome (DInt 9007199254740000).
Proof. vm_compute. reflexivity. Qed.

(** 1000 * s at the edge where it no longer fits: 2^60 * 1000 > int64_max. *)
Theorem mul_checked_seconds_overflow :
  apply_prim PMulChecked [DInt 1000; DInt 1152921504606846976] = DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem mul_checked_mismatch :
  apply_prim PMulChecked [DBytes (list_ascii_of_string "2"); DInt 2] = DNone.
Proof. vm_compute. reflexivity. Qed.

(* ===== §7  R8 CONFIRMATION: error payloads are arbitrary dvals ============= *)

(** R8 = "error values carry arbitrary dvals, including byte-string messages". This has
    been TRUE since R1/M1 — [OThrow] evaluates any val and [OErr e] carries any dval —
    but no theorem pinned it. These make it deliberate; R8 needs NO new machinery.

    The payload bytes are pinned EXACTLY (the literal message, not a name). *)
Theorem throw_bytes_payload_exact :
  let '(o, _) := run_top DUnit 0 sample_throw_bytes in
  o = OErr (DBytes (list_ascii_of_string "boom: k missing")).
Proof. vm_compute. reflexivity. Qed.

(** The pre-throw put commits; the exact byte message is the observable error. *)
Theorem throw_bytes_commits_prefix :
  observe DUnit 0 sample_throw_bytes
  = (OErr (DBytes (list_ascii_of_string "boom: k missing")),
     [("1"%string, (DInt 1, None))], []).
Proof. vm_compute. reflexivity. Qed.

(** A STRUCTURED error payload: DTag 2 over a (message bytes, code) pair — consumers
    can carry error codes + messages without any IR change. *)
Theorem throw_tagged_payload_exact :
  let '(o, _) := run_top DUnit 0 sample_throw_tagged in
  o = OErr (DTag 2 (DPair (DBytes (list_ascii_of_string "boom: k missing"))
                          (DInt 404))).
Proof. vm_compute. reflexivity. Qed.

(* ===== §8  Inhabitance ===================================================== *)

(** A context satisfying the end-to-end theorem's precondition exists, and the run
    lands on the stated outcome — explicit witness (snd of the closed run), vm_compute
    only on a closed term. *)
Lemma fold_put_inhabited :
  exists w, run_top mixed_ctx 0 sample_fold_put = (ORet (DInt 3), w).
Proof.
  exists (snd (run_top mixed_ctx 0 sample_fold_put)).
  vm_compute. reflexivity.
Qed.

(** A poison-carrying list exists on which the guard genuinely throws. *)
Lemma fold_guard_inhabited :
  exists w, run_top guard_ctx 0 sample_fold_guard = (OErr (DBytes poison_bytes), w).
Proof.
  exists (snd (run_top guard_ctx 0 sample_fold_guard)).
  vm_compute. reflexivity.
Qed.

(** Print Assumptions footprint — each must say "Closed under the global context". *)
Print Assumptions fold_mixed_end_to_end.
Print Assumptions fold_concat_forward.
Print Assumptions fold_concat_reversed.
Print Assumptions fold_concat_order_observable.
Print Assumptions fold_trace_forward.
Print Assumptions fold_trace_reversed.
Print Assumptions fold_trace_order_observable.
Print Assumptions mutant_foldr_concat.
Print Assumptions mutant_foldr_observably_differs.
Print Assumptions fold_guard_short_circuit.
Print Assumptions fold_guard_poison_first.
Print Assumptions fold_init_throw_short_circuits.
Print Assumptions fold_non_list_yields_init.
Print Assumptions fold_non_list_runs_init_effects.
Print Assumptions fold_empty_list_yields_init.
Print Assumptions fold_singleton.
Print Assumptions fold_acc_overflow.
Print Assumptions fold_ovf_empty_list.
Print Assumptions list_len_three.
Print Assumptions list_len_empty.
Print Assumptions list_len_mismatch_shape.
Print Assumptions list_len_mismatch_arity.
Print Assumptions list_nth_neg_one.
Print Assumptions list_nth_zero.
Print Assumptions list_nth_len_minus_one.
Print Assumptions list_nth_len.
Print Assumptions list_nth_empty.
Print Assumptions list_nth_huge_index.
Print Assumptions list_nth_mismatch_index.
Print Assumptions list_nth_mismatch_list.
Print Assumptions mul_checked_max_times_two.
Print Assumptions mul_checked_neg_one_times_min.
Print Assumptions mul_checked_min_times_neg_one.
Print Assumptions mul_checked_max_times_one.
Print Assumptions mul_checked_min_times_one.
Print Assumptions mul_checked_seconds_to_ms.
Print Assumptions mul_checked_seconds_overflow.
Print Assumptions mul_checked_mismatch.
Print Assumptions throw_bytes_payload_exact.
Print Assumptions throw_bytes_commits_prefix.
Print Assumptions throw_tagged_payload_exact.
Print Assumptions fold_put_inhabited.
Print Assumptions fold_guard_inhabited.


