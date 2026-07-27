(** * FileIO — C3 (adr-0017): laws, THE chunking-invariance principle, and the
    proven wc-core.

    The reasoning model in action (adr-0017 §Reasoning model):
    - [chunking_invariance]: reading a stream in chunks of ANY size [ml >= 1]
      reassembles the stream — buffer size is a provably unobservable choice.
      Proven pure (over [file_chunk]'s firstn/skipn), then lifted through [run]
      by the wc loop invariant.
    - [wc_prog_correct]: the wc-core program (Samples.v [wc_prog]) computes
      EXACTLY the byte count of the opened file, for every path, contents, fuel
      and chunk size with [length cs <= fuel * ml] — the invariant threads the
      counter through the store and the offset through the descriptor table.
    - Anti-vacuity (adr-0005): EOF boundary instances at [len = k*ml - 1 / k*ml /
      k*ml + 1] (vm_compute), a WRONG-CHUNKING mutant (counts [ml] instead of the
      chunk's length — overcounts at EOF) observably rejected exactly at the
      boundary, and the correct-program instances double as execution witnesses.

    Print Assumptions must read "Closed under the global context" throughout. *)

From Stdlib Require Import ZArith List String Ascii Bool Lia FMapFacts OrderedTypeEx.
From Rocqeteer Require Import EffIR Samples Journal.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation length := List.length.

Module FF := FMapFacts.WFacts_fun(String_as_OT)(M).

(* ===== §1  Pure chunk arithmetic ============================================ *)

Lemma file_chunk_length : forall cs off ml,
  length (file_chunk cs off ml)
  = Nat.min (Z.to_nat ml) (length cs - Z.to_nat off)%nat.
Proof.
  intros cs off ml. unfold file_chunk.
  rewrite length_firstn, length_skipn. reflexivity.
Qed.

(** The chunk stream a bounded reader sees: successive [ml]-sized windows. *)
Fixpoint chunk_stream (cs : list ascii) (off ml fuel : nat) : list (list ascii) :=
  match fuel with
  | O      => []
  | S f    => firstn ml (skipn off cs) :: chunk_stream cs (off + ml) ml f
  end.

(** THE PRINCIPLE (generalized over the start offset for the induction): enough
    fuel reassembles the suffix exactly — no byte lost, none duplicated, for ANY
    chunk size >= 1. *)
Lemma chunk_stream_concat : forall fuel cs off ml,
  (1 <= ml)%nat -> (length cs <= off + fuel * ml)%nat ->
  List.concat (chunk_stream cs off ml fuel) = skipn off cs.
Proof.
  induction fuel as [| f IH]; intros cs off ml Hml Hlen; cbn.
  - symmetry. apply skipn_all2. lia.
  - rewrite (IH cs (off + ml)%nat ml Hml) by lia.
    rewrite <- (firstn_skipn ml (skipn off cs)) at 2.
    rewrite skipn_skipn. do 2 f_equal. lia.
Qed.

Theorem chunking_invariance : forall fuel cs ml,
  (1 <= ml)%nat -> (length cs <= fuel * ml)%nat ->
  List.concat (chunk_stream cs 0 ml fuel) = cs.
Proof.
  intros fuel cs ml Hml Hlen.
  rewrite (chunk_stream_concat fuel cs 0 ml Hml) by lia.
  reflexivity.
Qed.

(* ===== §2  Descriptor-table lemmas ========================================== *)

Lemma fd_find_set : forall fd e l, fd_find fd (fd_set fd e l) = Some e.
Proof.
  intros fd e l; induction l as [| [n e'] l' IH]; cbn.
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (Z.eqb n fd) eqn:En; cbn; rewrite En; [reflexivity | exact IH].
Qed.

(** One-step Bind equation (definitional) — the top-down stepping tool that keeps
    the abstract-fuel [Repeat] node intact until [run_repeat_eq] can name it. *)
Lemma run_bind_eq : forall env t1 t2 w,
  run env (Bind t1 t2) w
  = match run env t1 w with
    | (ORet x, w') => run (x :: env) t2 w'
    | (OErr e, w') => (OErr e, w')
    end.
Proof. reflexivity. Qed.

(* ===== §3  The wc loop invariant ============================================ *)
(* Explicit parameters throughout (no Section Variables — the check_no_admitted
   gate greps assumption vernaculars conservatively, and the house style is
   explicit binders anyway). *)

(** Offset/counter after [i] iterations: [min (i*ml) len], in nat. *)
Definition off_at (cs : list ascii) (ml : Z) (i : nat) : nat :=
  Nat.min (i * Z.to_nat ml) (length cs).

(** What the loop needs of a world — nothing more (the final answer reads the
    counter only): counter binding, descriptor position, contents in place. *)
Definition wcinv (pathb cs : list ascii) (ml nf : Z) (i : nat) (w : world) : Prop :=
  M.find (string_of_list_ascii wc_key) w.(kv)
    = Some (DInt (Z.of_nat (off_at cs ml i)), None)
  /\ fd_find nf w.(fds)
     = Some (string_of_list_ascii pathb, (Z.of_nat (off_at cs ml i), 0))
  /\ M.find (string_of_list_ascii pathb) w.(files) = Some cs.

(** The Repeat-body environment at the loop (Samples.v [wc_prog]):
    put-result · fd · open-result · path. *)
Definition wc_env (pathb : list ascii) (nf : Z) : list dval :=
  [DUnit; DInt nf; DTag 0 (DInt nf); DBytes pathb].

Lemma off_at_step : forall cs ml i, 1 <= ml ->
  (off_at cs ml i
   + Nat.min (Z.to_nat ml) (length cs - off_at cs ml i))%nat = off_at cs ml (S i).
Proof.
  intros cs ml i Hml; unfold off_at.
  assert (0 < Z.to_nat ml)%nat by lia. cbn [Nat.mul]. lia.
Qed.

Lemma wc_body_step : forall pathb cs ml nf i w,
  1 <= ml ->
  Z.of_nat (length cs) <= 9223372036854775807 ->
  wcinv pathb cs ml nf i w ->
  exists w', run (wc_env pathb nf) (wc_body 1 ml) w = (ORet DUnit, w')
             /\ wcinv pathb cs ml nf (S i) w'.
Proof.
  intros pathb cs ml nf i w Hml Hlen (Hc & Hf & Hfl).
  unfold wc_body. cbn.
  rewrite Hf, Hfl.
  destruct (Z.leb ml 0) eqn:Eml; [apply Z.leb_le in Eml; lia |].
  cbn.
  set (chunk := file_chunk cs (Z.of_nat (off_at cs ml i)) ml).
  unfold find_live. cbn in Hc. rewrite Hc. cbn.
  assert (Hchunklen : (length chunk
                       = Nat.min (Z.to_nat ml) (length cs - off_at cs ml i))%nat).
  { unfold chunk. rewrite file_chunk_length. do 2 f_equal. lia. }
  assert (Hoffle : (off_at cs ml i <= length cs)%nat) by (unfold off_at; lia).
  assert (Hsum : Z.of_nat (off_at cs ml i) + Z.of_nat (length chunk)
                 = Z.of_nat (off_at cs ml (S i))).
  { rewrite Hchunklen. rewrite <- (off_at_step cs ml i Hml). lia. }
  assert (Hoff_le : (off_at cs ml (S i) <= length cs)%nat) by (unfold off_at; lia).
  unfold apply_add_checked. rewrite Hsum.
  assert (Hrange : in_range (Z.of_nat (off_at cs ml (S i))) = true).
  { unfold in_range, int64_min, int64_max.
    apply andb_true_intro; split; apply Z.leb_le; lia. }
  rewrite Hrange. cbn.
  eexists. split; [reflexivity |].
  repeat split.
  - cbn -[M.find M.add]. rewrite FF.add_eq_o by reflexivity. reflexivity.
  - cbn -[M.find M.add]. rewrite fd_find_set. reflexivity.
  - cbn -[M.find M.add]. exact Hfl.
Qed.

Lemma wc_loop : forall pathb cs ml nf m j w,
  1 <= ml ->
  Z.of_nat (length cs) <= 9223372036854775807 ->
  wcinv pathb cs ml nf j w ->
  exists w', repeat_loop (wc_env pathb nf) (wc_body 1 ml) m w = (ORet DUnit, w')
             /\ wcinv pathb cs ml nf (j + m)%nat w'.
Proof.
  intros pathb cs ml nf m; induction m as [| m' IH]; intros j w Hml Hlen Hw;
    cbn [repeat_loop].
  - exists w. split; [reflexivity | now rewrite Nat.add_0_r].
  - destruct (wc_body_step pathb cs ml nf j w Hml Hlen Hw) as (w1 & Hrun & Hinv).
    rewrite Hrun.
    destruct (IH (S j) w1 Hml Hlen Hinv) as (w2 & Hrun2 & Hinv2).
    exists w2. split; [exact Hrun2 |].
    replace (j + S m')%nat with (S j + m')%nat by lia. exact Hinv2.
Qed.

(** THE THEOREM: the wc-core computes exactly the byte count — for EVERY path,
    contents, fuel and chunk size covering the file (adr-0017 reasoning model:
    the chunking is provably unobservable). *)
Theorem wc_prog_correct : forall (pathb cs : list ascii) (ml nf : Z)
                                 (fuel : nat) (w0 : world),
  1 <= ml ->
  Z.of_nat (length cs) <= 9223372036854775807 ->
  (length cs <= fuel * Z.to_nat ml)%nat ->
  w0.(ctx) = DBytes pathb ->
  M.find (string_of_list_ascii pathb) w0.(files) = Some cs ->
  w0.(fds) = [] ->
  w0.(next_fd) = nf ->
  fst (run [] (wc_prog fuel ml) w0) = ORet (DInt (Z.of_nat (length cs))).
Proof.
  intros pathb cs ml nf fuel w0 Hml Hlen Hfuel Hctx Hfilesw Hfds Hnf.
  unfold wc_prog.
  rewrite run_bind_eq.
  assert (Eask : run [] (Perform OAsk []) w0 = (ORet w0.(ctx), w0))
    by reflexivity.
  rewrite Eask, Hctx.
  rewrite run_bind_eq.
  set (W1 := set_io w0 w0.(files)
               (fd_set nf (string_of_list_ascii pathb, (0, 0)) []) (Z.succ nf)).
  assert (Eopen : run [DBytes pathb] (Perform OOpen [VVar 0; VInt 0]) w0
                  = (ORet (DTag 0 (DInt nf)), W1)).
  { cbn -[fd_set]. rewrite Hfilesw, Hfds, Hnf. reflexivity. }
  rewrite Eopen.
  rewrite run_match_eq. cbn [eval_val nth try_branches match_pat].
  rewrite Z.eqb_refl. cbn [push_env fold_left].
  rewrite run_bind_eq.
  set (W2 := set_kv W1 (M.add (string_of_list_ascii wc_key) (DInt 0, None)
                          W1.(kv))).
  assert (Eput : run [DInt nf; DTag 0 (DInt nf); DBytes pathb]
                   (Perform OPut [VBytes wc_key; VInt 0]) W1
                 = (ORet DUnit, W2)) by reflexivity.
  rewrite Eput.
  rewrite run_bind_eq, run_repeat_eq.
  assert (Hinv0 : wcinv pathb cs ml nf 0 W2).
  { repeat split.
    - unfold W2. cbn -[M.find M.add].
      rewrite FF.add_eq_o by reflexivity.
      unfold off_at. cbn. reflexivity.
    - unfold W2, W1. cbn -[M.find M.add]. rewrite Z.eqb_refl.
      unfold off_at. cbn. reflexivity.
    - unfold W2, W1. cbn -[M.find M.add]. exact Hfilesw. }
  destruct (wc_loop pathb cs ml nf fuel 0%nat W2 Hml Hlen Hinv0)
    as (w2 & Hrun2 & Hinv2).
  change (DUnit :: [DInt nf; DTag 0 (DInt nf); DBytes pathb])
    with (wc_env pathb nf).
  rewrite Hrun2.
  destruct Hinv2 as (Hc2 & Hf2 & _).
  assert (Hfull : off_at cs ml (0 + fuel)%nat = length cs)
    by (unfold off_at; lia).
  rewrite Hfull in Hc2.
  rewrite run_bind_eq.
  assert (Eclose : run (DUnit :: wc_env pathb nf) (Perform OClose [VVar 2]) w2
                   = (ORet (DBool true),
                      set_io w2 w2.(files) (fd_remove nf w2.(fds))
                        w2.(next_fd))).
  { cbn -[fd_find fd_remove]. rewrite Hf2. reflexivity. }
  rewrite Eclose.
  rewrite run_bind_eq.
  assert (Eget : run (DBool true :: DUnit :: wc_env pathb nf)
                   (Perform OGet [VBytes wc_key])
                   (set_io w2 w2.(files) (fd_remove nf w2.(fds)) w2.(next_fd))
                 = (ORet (DSome (DInt (Z.of_nat (length cs)))),
                    set_kv (set_io w2 w2.(files) (fd_remove nf w2.(fds))
                              w2.(next_fd))
                      (set_io w2 w2.(files) (fd_remove nf w2.(fds))
                         w2.(next_fd)).(kv))).
  { cbn -[M.find]. unfold find_live. cbn -[M.find].
    cbn in Hc2. rewrite Hc2. reflexivity. }
  rewrite Eget.
  rewrite run_match_eq. cbn. reflexivity.
Qed.

(* ===== §4  Anti-vacuity (adr-0005): boundaries, mutant, witnesses =========== *)

Definition fio_path : list ascii := list_ascii_of_string "f".

Definition fio_world (cs : list ascii) : world :=
  mkWorld (M.empty entry) (DBytes fio_path) 0 [] (M.empty dval) []
          (M.add (string_of_list_ascii fio_path) cs (M.empty (list ascii))) [] 3
          [] [] [] 1.

Definition bytes_n (n : nat) : list ascii := repeat "a"%char n.

(** EOF boundaries around a chunk multiple (ml = 3, fuel = 8): k*ml - 1 / k*ml /
    k*ml + 1 — the chunk clipping is exact on all three. *)
Theorem wc_boundary_below :
  fst (run [] (wc_prog 8 3) (fio_world (bytes_n 5))) = ORet (DInt 5).
Proof. vm_compute. reflexivity. Qed.

Theorem wc_boundary_at :
  fst (run [] (wc_prog 8 3) (fio_world (bytes_n 6))) = ORet (DInt 6).
Proof. vm_compute. reflexivity. Qed.

Theorem wc_boundary_above :
  fst (run [] (wc_prog 8 3) (fio_world (bytes_n 7))) = ORet (DInt 7).
Proof. vm_compute. reflexivity. Qed.

Theorem wc_empty :
  fst (run [] (wc_prog 8 3) (fio_world (bytes_n 0))) = ORet (DInt 0).
Proof. vm_compute. reflexivity. Qed.

(** The modeled-error VALUES really flow: missing path -> Tag(1,2); stale fd ->
    Tag(1,9) — a program can branch on both, no abort. *)
Theorem file_missing_values :
  fst (run [] sample_file_missing (init_world DUnit 0))
  = ORet (DPair (DTag 1 (DInt 2)) (DTag 1 (DInt 9))).
Proof. vm_compute. reflexivity. Qed.

(** MUTANT (adr-0005): count the REQUESTED size [ml] instead of the returned
    chunk's length — correct on chunk-multiple files, overcounts at EOF. *)
Definition wc_body_mutant (fd_idx : nat) (ml : Z) : tm :=
  Bind (Perform ORead [VVar fd_idx; VInt ml])
    (Bind (Ret (VInt ml))                                (* MUTANT: not the chunk *)
       (Bind (Perform OGet [VBytes wc_key])
          (Match (VVar 0)
             [(PSome,
               Bind (Prim PAddChecked [VVar 0; VVar 2])
                 (Match (VVar 0)
                    [(PSome, Perform OPut [VBytes wc_key; VVar 0])]
                    (Perform OThrow [VBytes (list_ascii_of_string "OVF")])))]
             (Perform OThrow [VBytes (list_ascii_of_string "NOCTR")])))).

Definition wc_prog_mutant (fuel : nat) (ml : Z) : tm :=
  Bind (Perform OAsk [])
    (Bind (Perform OOpen [VVar 0; VInt 0])
       (Match (VVar 0)
          [(PTag 0,
            Bind (Perform OPut [VBytes wc_key; VInt 0])
              (Bind (Repeat fuel (wc_body_mutant 1 ml))
                 (Bind (Perform OClose [VVar 2])
                    (Bind (Perform OGet [VBytes wc_key])
                       (Match (VVar 0)
                          [(PSome, Ret (VVar 0))]
                          (Perform OThrow
                             [VBytes (list_ascii_of_string "NOCTR")]))))))]
          (Perform OThrow [VVar 0]))).

(** Rejected exactly at the EOF boundary (5 is not a multiple of 3)... *)
Theorem wc_mutant_rejected :
  fst (run [] (wc_prog_mutant 8 3) (fio_world (bytes_n 5)))
  <> fst (run [] (wc_prog 8 3) (fio_world (bytes_n 5))).
Proof. vm_compute. intro H; discriminate H. Qed.

(** ... and PLAUSIBLE away from it: on a fuel*ml-sized file the two agree. *)
Theorem wc_mutant_plausible :
  fst (run [] (wc_prog_mutant 8 3) (fio_world (bytes_n 24)))
  = fst (run [] (wc_prog 8 3) (fio_world (bytes_n 24))).
Proof. vm_compute. reflexivity. Qed.

(* ===== §5  Print Assumptions ================================================ *)

(** Each must read "Closed under the global context". *)
Print Assumptions chunking_invariance.
Print Assumptions wc_prog_correct.
Print Assumptions wc_boundary_below.
Print Assumptions wc_boundary_at.
Print Assumptions wc_boundary_above.
Print Assumptions wc_empty.
Print Assumptions file_missing_values.
Print Assumptions wc_mutant_rejected.
Print Assumptions wc_mutant_plausible.
