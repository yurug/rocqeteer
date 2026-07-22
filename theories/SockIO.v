(** * SockIO — C4 (adr-0018): the HTTP response spec and the server smoke tests.

    [http_response] is the pure Gallina response function the server program must
    compute per connection; [encode_table] is the ctx encoding (a [DList] of
    [DPair path body]).  The vm instances below run [sample_http] end-to-end
    against a scripted world and pin the WHOLE transcript — they are the cheap
    validator of the program's de Bruijn plumbing, ahead of the general theorem. *)

From Stdlib Require Import ZArith List String Ascii Bool Lia.
From Rocqeteer Require Import EffIR Samples Journal Wf FileIO.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation length := List.length.

(* ===== §1  The response spec ================================================ *)

Fixpoint route_lookup (tbl : list (list ascii * list ascii)) (p : list ascii)
  : option (list ascii) :=
  match tbl with
  | []            => None
  | (q, b) :: t'  => if ascii_list_eqb q p then Some b else route_lookup t' p
  end.

Definition digits_of (n : Z) : list ascii :=
  match apply_print_int n with
  | DSome (DBytes ds) => ds
  | _                 => []
  end.

Definition resp_200 (b : list ascii) : list ascii :=
  resp200_pre ++ digits_of (Z.of_nat (length b)) ++ crlfcrlf ++ b.

(** The reference response function — mirrors the program arm for arm:
    no CRLF -> 400; request line shorter than "GET " or not GET -> 400;
    no space after the path -> 400; then the route table decides 200/404. *)
Definition http_response (tbl : list (list ascii * list ascii))
    (req : list ascii) : list ascii :=
  match find_sub crlf req with
  | None   => resp_400
  | Some i =>
      let line := firstn i req in
      if (4 <=? length line)%nat then
        if ascii_list_eqb (firstn 4 line) get_sp then
          let rest := skipn 4 line in
          match find_sub sp1 rest with
          | None   => resp_400
          | Some j =>
              let p := firstn j rest in
              match route_lookup tbl p with
              | Some b => resp_200 b
              | None   => resp_404
              end
          end
        else resp_400
      else resp_400
  end.

Definition encode_table (tbl : list (list ascii * list ascii)) : dval :=
  DList (map (fun qb => DPair (DBytes (fst qb)) (DBytes (snd qb))) tbl).

(** What a run must leave in the transcript: connection ids from [S j], in script
    order, each with its input and the spec response. *)
Fixpoint elog (tbl : list (list ascii * list ascii)) (j : nat)
    (sc : list (list ascii)) : ctranscript :=
  match sc with
  | []       => []
  | r :: sc' => (Z.of_nat (S j), (r, http_response tbl r)) :: elog tbl (S j) sc'
  end.

Definition expected_log (tbl : list (list ascii * list ascii))
    (script : list (list ascii)) : ctranscript :=
  elog tbl 0 script.

(* ===== §2  Smoke: the whole transcript, pinned by vm_compute ================ *)

Definition tb : list (list ascii * list ascii) :=
  [ (list_ascii_of_string "/", list_ascii_of_string "home");
    (list_ascii_of_string "/x", list_ascii_of_string "payload") ].

Definition req_ok : list ascii :=
  list_ascii_of_string "GET /x HTTP/1.0" ++ crlf ++ crlf.
Definition req_404 : list ascii :=
  list_ascii_of_string "GET /nope HTTP/1.0" ++ crlf ++ crlf.
Definition req_bad : list ascii := list_ascii_of_string "junk".

(** Three connections: a hit, a miss, a malformed request — the transcript equals
    the spec on all three (ids 1..3, inputs preserved, responses exact). *)
Theorem sock_smoke :
  observe_sock (encode_table tb) [req_ok; req_404; req_bad] sample_http
  = (ORet DUnit, expected_log tb [req_ok; req_404; req_bad]).
Proof. vm_compute. reflexivity. Qed.

(** Chunk-boundary corner: the FIRST CRLF straddling the 7-byte recv boundary
    (request line of exactly 13 bytes puts the CRLF at bytes 13..14, split across
    chunks 2 and 3) — the accumulate-then-parse discipline is immune. *)
Definition req_straddle : list ascii :=
  list_ascii_of_string "GET / HTTP1.0" ++ crlf ++ crlf.

Theorem sock_smoke_straddle :
  observe_sock (encode_table tb) [req_straddle] sample_http
  = (ORet DUnit, expected_log tb [req_straddle]).
Proof. vm_compute. reflexivity. Qed.

(** Script exhaustion is a no-op, not an error: fewer connections than fuel. *)
Theorem sock_smoke_exhausted :
  observe_sock (encode_table tb) [req_ok] sample_http
  = (ORet DUnit, expected_log tb [req_ok]).
Proof. vm_compute. reflexivity. Qed.

(* ===== §3  Groundwork: prim spec lemmas ===================================== *)

Lemma is_prefix_length : forall n h,
  is_prefix n h = true -> (length n <= length h)%nat.
Proof.
  induction n as [| c n' IH]; intros h H; cbn; [lia |].
  destruct h as [| d h']; cbn in H; [discriminate |].
  apply andb_true_iff in H as [_ H]. specialize (IH _ H). cbn. lia.
Qed.

Lemma find_sub_bound : forall n h i,
  find_sub n h = Some i -> (i + length n <= length h)%nat.
Proof.
  intros n h; revert n; induction h as [| d h' IH]; intros n i H; cbn in H.
  - destruct (is_prefix n []) eqn:Ep; [| discriminate].
    injection H as <-. apply is_prefix_length in Ep. cbn in Ep |- *. lia.
  - destruct (is_prefix n (d :: h')) eqn:Ep.
    + injection H as <-. apply is_prefix_length in Ep. cbn in Ep |- *. lia.
    + destruct (find_sub n h') as [i' |] eqn:Ef; cbn in H; [| discriminate].
      injection H as <-. specialize (IH _ _ Ef). cbn. lia.
Qed.

(** In-range [PBytesSub] computes the slice. *)
Lemma bytes_sub_in_range : forall bs (off len : nat),
  (off + len <= length bs)%nat ->
  apply_bytes_sub bs (Z.of_nat off) (Z.of_nat len)
  = DSome (DBytes (firstn len (skipn off bs))).
Proof.
  intros bs off len H. unfold apply_bytes_sub.
  destruct (Z.ltb (Z.of_nat off) 0) eqn:E1; [apply Z.ltb_lt in E1; lia |].
  destruct (Z.ltb (Z.of_nat len) 0) eqn:E2; [apply Z.ltb_lt in E2; lia |].
  destruct (Z.ltb (Z.of_nat (length bs)) (Z.of_nat off + Z.of_nat len)) eqn:E3.
  - apply Z.ltb_lt in E3; lia.
  - cbn. rewrite !Nat2Z.id. reflexivity.
Qed.

Lemma print_int_in_range : forall z,
  0 <= z <= int64_max -> exists ds, apply_print_int z = DSome (DBytes ds).
Proof.
  intros z Hz. unfold apply_print_int.
  destruct (in_range z) eqn:Er.
  - cbn [negb]. eexists. reflexivity.
  - unfold in_range, int64_min, int64_max in Er. unfold int64_max in Hz.
    apply andb_false_iff in Er as [E | E]; apply Z.leb_gt in E; lia.
Qed.

(* ===== §4  Route correctness ================================================ *)

Lemma route_lookup_forall :
  forall (Q : list ascii -> Prop) tbl p b,
    Forall (fun qb => Q (snd qb)) tbl ->
    route_lookup tbl p = Some b -> Q b.
Proof.
  intros Q tbl p b HF; induction HF as [| [q b'] t Hh HF IH]; cbn; intros Er;
    [discriminate |].
  destruct (ascii_list_eqb q p).
  - injection Er as <-. exact Hh.
  - apply IH; exact Er.
Qed.

(** The dval an option-of-body accumulator denotes. *)
Definition accd (o : option (list ascii)) : dval :=
  match o with None => DNone | Some b => DSome (DBytes b) end.

(** The named fold twin runs the route body to exactly [route_lookup], first hit
    sticking, world untouched. *)
Lemma route_fold_correct : forall tbl p (X : dval) env w o,
  fold_elems (X :: DBytes p :: env)
    (Match (VVar 0)
       [(PSome, Ret (VSome (VVar 0)))]
       (Match (VVar 1)
          [(PPair,
            Bind (Prim PEqBytes [VVar 1; VVar 5])
              (Match (VVar 0)
                 [(PBool true, Ret (VSome (VVar 1)))]
                 (Ret VNone)))]
          (Ret VNone)))
    (map (fun qb => DPair (DBytes (fst qb)) (DBytes (snd qb))) tbl)
    (accd o) w
  = (ORet (accd (match o with
                 | Some b => Some b
                 | None   => route_lookup tbl p
                 end)), w).
Proof.
  induction tbl as [| [q b] t IH]; intros p X env w o.
  - cbn. destruct o; reflexivity.
  - cbn [map fst snd]. rewrite fold_elems_cons.
    destruct o as [b0 |]; cbn -[fold_elems].
    + pose proof (IH p X env w (Some b0)) as IHs; cbn [accd] in IHs.
      rewrite IHs. reflexivity.
    + destruct (ascii_list_eqb q p) eqn:Eq; cbn -[fold_elems].
      * pose proof (IH p X env w (Some b)) as IHs; cbn [accd] in IHs.
        rewrite IHs. reflexivity.
      * pose proof (IH p X env w None) as IHs; cbn [accd] in IHs.
        rewrite IHs. reflexivity.
Qed.

(** [http_route]: with the PATH at de Bruijn 0 and the encoded table in the ctx,
    the subtree computes the spec's 200/404 — world untouched. *)
Lemma http_route_correct : forall p env w tbl,
  w.(ctx) = encode_table tbl ->
  Forall (fun qb => Z.of_nat (length (snd qb)) <= int64_max) tbl ->
  run (DBytes p :: env) http_route w
  = (ORet (DBytes (match route_lookup tbl p with
                   | Some b => resp_200 b
                   | None   => resp_404
                   end)), w).
Proof.
  intros p env w tbl Hctx Htbl.
  unfold http_route.
  rewrite run_bind_eq.
  assert (Eask : run (DBytes p :: env) (Perform OAsk []) w = (ORet w.(ctx), w))
    by reflexivity.
  rewrite Eask, Hctx.
  rewrite run_bind_eq, run_fold_eq. cbn [run eval_val nth].
  unfold encode_table.
  rewrite (route_fold_correct tbl p _ env w None).
  destruct (route_lookup tbl p) as [b |] eqn:Er; cbn.
  - (* 200: the body is in the table, so its length is printable *)
    assert (Hb : Z.of_nat (length b) <= int64_max)
      by (exact (route_lookup_forall
                    (fun x => Z.of_nat (length x) <= int64_max) tbl p b Htbl Er)).
    destruct (print_int_in_range (Z.of_nat (length b)))
      as [ds Hds]; [lia |].
    cbn. rewrite Hds. cbn.
    unfold resp_200, digits_of. rewrite Hds.
    rewrite <- !app_assoc. reflexivity.
  - reflexivity.
Qed.

(* ===== §5  Parse correctness ================================================ *)

(** [http_parse]: with the accumulated request at de Bruijn 0 and the encoded
    table in the ctx, the subtree computes EXACTLY [http_response] — pure (world
    untouched).  Proof: the spec and the program share their scrutinees
    ([find_sub], the length test, the prefix test), so each destruct steps both
    sides in lockstep; the in-range rewrites discharge the sub/print guards. *)
Lemma http_parse_correct : forall req env w tbl,
  w.(ctx) = encode_table tbl ->
  Z.of_nat (length req) <= int64_max ->
  Forall (fun qb => Z.of_nat (length (snd qb)) <= int64_max) tbl ->
  run (DBytes req :: env) http_parse w
  = (ORet (DBytes (http_response tbl req)), w).
Proof.
  intros req env w tbl Hctx Hreq Htbl.
  unfold http_parse, http_response.
  cbn -[http_route apply_bytes_sub apply_sub_checked apply_print_int Nat.leb ascii_list_eqb firstn skipn find_sub route_lookup get_sp sp1 crlf crlfcrlf resp_400 resp_404 resp200_pre resp_200].
  destruct (find_sub crlf req) as [i |] eqn:E1;
    cbn -[http_route apply_bytes_sub apply_sub_checked apply_print_int Nat.leb ascii_list_eqb firstn skipn find_sub route_lookup get_sp sp1 crlf crlfcrlf resp_400 resp_404 resp200_pre resp_200];
    [| reflexivity].
  pose proof (find_sub_bound _ _ _ E1) as Hi; cbn [length crlf] in Hi.
  assert (Es1 : apply_bytes_sub req 0 (Z.of_nat i)
                = DSome (DBytes (firstn i req))).
  { replace 0 with (Z.of_nat 0) by reflexivity.
    rewrite bytes_sub_in_range by lia.
    rewrite skipn_O. reflexivity. }
  rewrite Es1; cbn -[http_route apply_bytes_sub apply_sub_checked apply_print_int Nat.leb ascii_list_eqb firstn skipn find_sub route_lookup get_sp sp1 crlf crlfcrlf resp_400 resp_404 resp200_pre resp_200].
  set (line := firstn i req) in *.
  assert (Hline : length line = i)
    by (unfold line; rewrite length_firstn; lia).
  destruct ((4 <=? length line)%nat) eqn:E2.
  - (* the request line is at least "GET " long *)
    apply Nat.leb_le in E2.
    assert (Es2 : apply_bytes_sub line 0 4 = DSome (DBytes (firstn 4 line))).
    { change 0 with (Z.of_nat 0). change 4 with (Z.of_nat 4).
      rewrite bytes_sub_in_range by lia.
      rewrite skipn_O. reflexivity. }
    rewrite Es2; cbn -[http_route apply_bytes_sub apply_sub_checked apply_print_int Nat.leb ascii_list_eqb firstn skipn find_sub route_lookup get_sp sp1 crlf crlfcrlf resp_400 resp_404 resp200_pre resp_200].
    destruct (ascii_list_eqb (firstn 4 line) get_sp) eqn:E3;
      cbn -[http_route apply_bytes_sub apply_sub_checked apply_print_int Nat.leb ascii_list_eqb firstn skipn find_sub route_lookup get_sp sp1 crlf crlfcrlf resp_400 resp_404 resp200_pre resp_200];
      [| reflexivity].
    assert (Es3 : apply_sub_checked (Z.of_nat (length line)) 4
                  = DSome (DInt (Z.of_nat (length line - 4)))).
    { unfold apply_sub_checked.
      assert (Hin : in_range (Z.of_nat (length line) - 4) = true).
      { unfold in_range, int64_min, int64_max.
        apply andb_true_intro; split; apply Z.leb_le.
        - lia.
        - unfold int64_max in Hreq. unfold line in *.
          rewrite length_firstn in *. lia. }
      rewrite Hin. do 2 f_equal. lia. }
    rewrite Es3; cbn -[http_route apply_bytes_sub apply_sub_checked apply_print_int Nat.leb ascii_list_eqb firstn skipn find_sub route_lookup get_sp sp1 crlf crlfcrlf resp_400 resp_404 resp200_pre resp_200].
    assert (Es4 : apply_bytes_sub line 4 (Z.of_nat (length line - 4))
                  = DSome (DBytes (skipn 4 line))).
    { change 4 with (Z.of_nat 4) at 1.
      rewrite bytes_sub_in_range by lia.
      rewrite firstn_all2; [reflexivity |].
      rewrite length_skipn. lia. }
    rewrite Es4; cbn -[http_route apply_bytes_sub apply_sub_checked apply_print_int Nat.leb ascii_list_eqb firstn skipn find_sub route_lookup get_sp sp1 crlf crlfcrlf resp_400 resp_404 resp200_pre resp_200].
    set (rest := skipn 4 line) in *.
    destruct (find_sub sp1 rest) as [j |] eqn:E4;
      cbn -[http_route apply_bytes_sub apply_sub_checked apply_print_int Nat.leb ascii_list_eqb firstn skipn find_sub route_lookup get_sp sp1 crlf crlfcrlf resp_400 resp_404 resp200_pre resp_200];
      [| reflexivity].
    pose proof (find_sub_bound _ _ _ E4) as Hj; cbn [length sp1] in Hj.
    assert (Es5 : apply_bytes_sub rest 0 (Z.of_nat j)
                  = DSome (DBytes (firstn j rest))).
    { replace 0 with (Z.of_nat 0) by reflexivity.
      rewrite bytes_sub_in_range by lia.
      rewrite skipn_O. reflexivity. }
    rewrite Es5; cbn -[http_route apply_bytes_sub apply_sub_checked apply_print_int Nat.leb ascii_list_eqb firstn skipn find_sub route_lookup get_sp sp1 crlf crlfcrlf resp_400 resp_404 resp200_pre resp_200].
    apply (http_route_correct (firstn j rest) _ w tbl Hctx Htbl).
  - (* line shorter than "GET ": the sub trips its guard, both sides 400 *)
    apply Nat.leb_gt in E2.
    assert (Es2 : apply_bytes_sub line 0 4 = DNone).
    { unfold apply_bytes_sub. cbn [Z.ltb].
      destruct (Z.ltb (Z.of_nat (length line)) (0 + 4)) eqn:Eg;
        [reflexivity | apply Z.ltb_ge in Eg; lia]. }
    rewrite Es2. reflexivity.
Qed.

(* ===== §6  The read loop and the per-connection theorem ===================== *)

Lemma firstn_chunk : forall (l : list ascii) a m,
  firstn a l ++ firstn m (skipn a l) = firstn (a + m) l.
Proof.
  intros l a; revert l; induction a as [| a IH]; intros l m; cbn.
  - reflexivity.
  - destruct l as [| x l']; cbn.
    + rewrite firstn_nil. reflexivity.
    + f_equal. apply IH.
Qed.

Definition roff (inp : list ascii) (ml : Z) (i : nat) : nat :=
  Nat.min (i * Z.to_nat ml) (length inp).

Lemma roff_step : forall inp ml i, 1 <= ml ->
  (roff inp ml i + Nat.min (Z.to_nat ml) (length inp - roff inp ml i))%nat
  = roff inp ml (S i).
Proof.
  intros inp ml i Hml; unfold roff.
  assert (0 < Z.to_nat ml)%nat by lia. cbn [Nat.mul]. lia.
Qed.

(** One read-loop iteration over the CANONICAL singleton world shape: only the
    store (the "b" buffer) and the connection's read offset move. *)
Lemma rc_body_step : forall c inp ml i env kvx
    c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0 lg0 nc0,
  1 <= ml ->
  Z.of_nat (length inp) <= int64_max ->
  M.find (string_of_list_ascii hbkey) kvx
    = Some ((DBytes (firstn (roff inp ml i) inp), None) : entry) ->
  exists kvx',
    run (DUnit :: DInt c :: env)
      (Bind (Perform ORecv [VVar 1; VInt ml])
         (Bind (Perform OGet [VBytes hbkey])
            (Match (VVar 0)
               [(PSome,
                 Bind (Prim PBytesConcat [VVar 0; VVar 2])
                   (Perform OPut [VBytes hbkey; VVar 0]))]
               (Perform OThrow [VBytes nobuf]))))
      (mkWorld kvx c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0
         [(c, (inp, (Z.of_nat (roff inp ml i), [])))] lg0 nc0)
    = (ORet DUnit,
       mkWorld kvx' c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0
         [(c, (inp, (Z.of_nat (roff inp ml (S i)), [])))] lg0 nc0)
    /\ M.find (string_of_list_ascii hbkey) kvx'
       = Some ((DBytes (firstn (roff inp ml (S i)) inp), None) : entry).
Proof.
  intros c inp ml i env kvx c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0 lg0 nc0
    Hml Hlen Hb.
  cbn -[M.find M.add file_chunk firstn].
  rewrite Z.eqb_refl.
  destruct (Z.leb ml 0) eqn:Eml; [apply Z.leb_le in Eml; lia |].
  cbn -[M.find M.add file_chunk firstn].
  unfold find_live. cbn in Hb. rewrite Hb.
  cbn -[M.find M.add file_chunk firstn].
  assert (Hofflen : Z.of_nat (roff inp ml i)
                    + Z.of_nat (length (file_chunk inp
                                          (Z.of_nat (roff inp ml i)) ml))
                    = Z.of_nat (roff inp ml (S i))).
  { rewrite file_chunk_length, Nat2Z.id.
    pose proof (roff_step inp ml i Hml). unfold roff in *. lia. }
  assert (Hcat : firstn (roff inp ml i) inp
                 ++ file_chunk inp (Z.of_nat (roff inp ml i)) ml
                 = firstn (roff inp ml (S i)) inp).
  { unfold file_chunk. rewrite Nat2Z.id, firstn_chunk.
    assert (Hsi : roff inp ml (S i)
                  = Nat.min (roff inp ml i + Z.to_nat ml) (length inp))
      by (unfold roff; lia).
    destruct (Nat.le_gt_cases (roff inp ml i + Z.to_nat ml) (length inp))
      as [Hc | Hc].
    - f_equal. lia.
    - rewrite firstn_all2 by lia. symmetry. apply firstn_all2. lia. }
  eexists. split.
  - unfold set_kv, set_sock. cbn -[M.find M.add file_chunk firstn].
    rewrite Hofflen. reflexivity.
  - cbn -[M.find M.add file_chunk firstn].
    rewrite FF.add_eq_o by reflexivity.
    rewrite Hcat. reflexivity.
Qed.

(* ===== §7  The handle and the accept loop =================================== *)

(** Folded one-step loop equation — keeps the recursive occurrence NAMED, so
    inductive hypotheses rewrite without normal-form fights. *)
Lemma repeat_loop_S : forall env body m w,
  repeat_loop env body (S m) w
  = match run env body w with
    | (ORet _, w1) => repeat_loop env body m w1
    | (OErr e, w1) => (OErr e, w1)
    end.
Proof. reflexivity. Qed.

Lemma rc_loop : forall c inp ml env m i kvx
    c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0 lg0 nc0,
  1 <= ml ->
  Z.of_nat (length inp) <= int64_max ->
  M.find (string_of_list_ascii hbkey) kvx
    = Some ((DBytes (firstn (roff inp ml i) inp), None) : entry) ->
  exists kvx',
    repeat_loop (DUnit :: DInt c :: env)
      (Bind (Perform ORecv [VVar 1; VInt ml])
         (Bind (Perform OGet [VBytes hbkey])
            (Match (VVar 0)
               [(PSome,
                 Bind (Prim PBytesConcat [VVar 0; VVar 2])
                   (Perform OPut [VBytes hbkey; VVar 0]))]
               (Perform OThrow [VBytes nobuf]))))
      m
      (mkWorld kvx c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0
         [(c, (inp, (Z.of_nat (roff inp ml i), [])))] lg0 nc0)
    = (ORet DUnit,
       mkWorld kvx' c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0
         [(c, (inp, (Z.of_nat (roff inp ml (i + m)), [])))] lg0 nc0)
    /\ M.find (string_of_list_ascii hbkey) kvx'
       = Some ((DBytes (firstn (roff inp ml (i + m)) inp), None) : entry).
Proof.
  intros c inp ml env m; induction m as [| m' IH];
    intros i kvx c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0 lg0 nc0 Hml Hlen Hb;
    cbn [repeat_loop].
  - exists kvx. rewrite Nat.add_0_r. split; [reflexivity | exact Hb].
  - destruct (rc_body_step c inp ml i env kvx
                c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0 lg0 nc0 Hml Hlen Hb)
      as (kv1 & Hrun & Hb1).
    rewrite Hrun.
    destruct (IH (S i) kv1 c0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0 lg0 nc0
                Hml Hlen Hb1) as (kv2 & Hrun2 & Hb2).
    exists kv2.
    replace (i + S m')%nat with (S i + m')%nat by lia.
    split; [exact Hrun2 | exact Hb2].
Qed.

(** ONE connection, handled: the transcript gains exactly the spec response; the
    connection table returns to empty; only the store evolves otherwise. *)
Lemma http_handle_correct : forall tbl c inp fr ml env kv0
    n0 tr0 ca0 j0 fl0 fd0 nf0 sc0 lg0 nc0,
  1 <= ml ->
  (length inp <= fr * Z.to_nat ml)%nat ->
  Z.of_nat (length inp) <= int64_max ->
  Forall (fun qb => Z.of_nat (length (snd qb)) <= int64_max) tbl ->
  exists kv',
    run (DInt c :: env) (http_handle fr ml)
      (mkWorld kv0 (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0 sc0
         [(c, (inp, (0, [])))] lg0 nc0)
    = (ORet (DBool true),
       mkWorld kv' (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0 sc0
         [] (lg0 ++ [(c, (inp, http_response tbl inp))]) nc0).
Proof.
  intros tbl c inp fr ml env kv0 n0 tr0 ca0 j0 fl0 fd0 nf0 sc0 lg0 nc0
    Hml Hfr Hlen Htbl.
  unfold http_handle.
  rewrite run_bind_eq.
  assert (Eput : run (DInt c :: env)
                   (Perform OPut [VBytes hbkey; VBytes []])
                   (mkWorld kv0 (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0
                      sc0 [(c, (inp, (0, [])))] lg0 nc0)
                 = (ORet DUnit,
                    mkWorld (M.add (string_of_list_ascii hbkey)
                               ((DBytes [], None) : entry) kv0)
                      (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0
                      sc0 [(c, (inp, (0, [])))] lg0 nc0))
    by reflexivity.
  rewrite Eput.
  rewrite run_bind_eq, run_repeat_eq.
  assert (Hb0 : M.find (string_of_list_ascii hbkey)
                  (M.add (string_of_list_ascii hbkey)
                     ((DBytes [], None) : entry) kv0)
                = Some ((DBytes (firstn (roff inp ml 0) inp), None) : entry)).
  { rewrite FF.add_eq_o by reflexivity. reflexivity. }
  destruct (rc_loop c inp ml env fr 0
              (M.add (string_of_list_ascii hbkey)
                 ((DBytes [], None) : entry) kv0)
              (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0 sc0 lg0 nc0
              Hml Hlen Hb0) as (kv1 & Hrun1 & Hb1).
  change (Z.of_nat (roff inp ml 0)) with 0 in Hrun1.
  rewrite Hrun1.
  assert (Hfull : roff inp ml (0 + fr) = length inp) by (unfold roff; lia).
  rewrite Hfull, firstn_all in Hb1.
  rewrite run_bind_eq.
  set (W2 := mkWorld kv1 (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0
               sc0 [(c, (inp, (Z.of_nat (roff inp ml (0 + fr)), [])))]
               lg0 nc0).
  assert (Eget : run (DUnit :: DUnit :: DInt c :: env)
                   (Perform OGet [VBytes hbkey]) W2
                 = (ORet (DSome (DBytes inp)), W2)).
  { unfold W2. cbn -[M.find M.add firstn roff].
    unfold find_live. cbn in Hb1. rewrite Hb1. reflexivity. }
  rewrite Eget.
  rewrite run_match_eq.
  cbn [eval_val nth try_branches match_pat push_env fold_left].
  rewrite run_bind_eq.
  rewrite (http_parse_correct inp _ _ tbl);
    [| reflexivity | exact Hlen | exact Htbl].
  set (resp := http_response tbl inp).
  rewrite run_bind_eq.
  assert (Esend : run (DBytes resp
                       :: DBytes inp :: DSome (DBytes inp) :: DUnit :: DUnit
                       :: DInt c :: env)
                    (Perform OSend [VVar 5; VVar 0]) W2
                  = (ORet DUnit,
                     mkWorld kv1 (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0
                       sc0
                       [(c, (inp, (Z.of_nat (roff inp ml (0 + fr)), resp)))]
                       lg0 nc0)).
  { unfold W2. cbn -[M.find M.add firstn roff].
    rewrite Z.eqb_refl. reflexivity. }
  rewrite Esend.
  exists kv1.
  cbn -[M.find M.add firstn roff]. rewrite Z.eqb_refl. reflexivity.
Qed.

(** Exhausted script: remaining accept iterations are no-ops. *)
Lemma accept_exhausted : forall fr ml m kv0 tbl
    n0 tr0 ca0 j0 fl0 fd0 nf0 lg0 nc0,
  repeat_loop []
    (Bind (Perform OAccept [])
       (Match (VVar 0) [(PTag 0, http_handle fr ml)] (Ret VUnit)))
    m
    (mkWorld kv0 (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0 [] [] lg0 nc0)
  = (ORet DUnit,
     mkWorld kv0 (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0 [] [] lg0 nc0).
Proof.
  intros; induction m as [| m' IH]; cbn [repeat_loop]; [reflexivity |].
  cbn -[M.find M.add http_handle]. exact IH.
Qed.

(** The accept loop consumes the whole script, ids counting up from [S j]. *)
Lemma http_accept_loop : forall tbl fr ml script m j kv0
    n0 tr0 ca0 j0 fl0 fd0 nf0 lg0,
  1 <= ml ->
  (List.length script <= m)%nat ->
  Forall (fun r => (length r <= fr * Z.to_nat ml)%nat
                   /\ Z.of_nat (length r) <= int64_max) script ->
  Forall (fun qb => Z.of_nat (length (snd qb)) <= int64_max) tbl ->
  exists kv',
    repeat_loop []
      (Bind (Perform OAccept [])
         (Match (VVar 0) [(PTag 0, http_handle fr ml)] (Ret VUnit)))
      m
      (mkWorld kv0 (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0
         script [] lg0 (Z.of_nat (S j)))
    = (ORet DUnit,
       mkWorld kv' (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0
         [] [] (lg0 ++ elog tbl j script)
         (Z.of_nat (S j + List.length script))).
Proof.
  intros tbl fr ml script; revert tbl fr ml;
    induction script as [| r sc' IH]; intros tbl fr ml m j kv0
      n0 tr0 ca0 j0 fl0 fd0 nf0 lg0 Hml Hm Hs Htbl.
  - exists kv0. cbn [elog List.length].
    rewrite app_nil_r, accept_exhausted, Nat.add_0_r. reflexivity.
  - destruct m as [| m']; cbn [List.length] in Hm; [lia |].
    inversion Hs as [| ? ? [Hr1 Hr2] Hs']; subst.
    rewrite repeat_loop_S, run_bind_eq.
    assert (Eacc : run [] (Perform OAccept [])
                     (mkWorld kv0 (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0
                        (r :: sc') [] lg0 (Z.of_nat (S j)))
                   = (ORet (DTag 0 (DInt (Z.of_nat (S j)))),
                      mkWorld kv0 (encode_table tbl) n0 tr0 ca0 j0 fl0 fd0 nf0
                        sc' [(Z.of_nat (S j), (r, (0, [])))] lg0
                        (Z.succ (Z.of_nat (S j))))) by reflexivity.
    rewrite Eacc.
    rewrite run_match_eq.
    cbn [eval_val nth try_branches match_pat push_env fold_left Z.eqb].
    replace (Z.succ (Z.of_nat (S j))) with (Z.of_nat (S (S j))) by lia.
    destruct (http_handle_correct tbl (Z.of_nat (S j)) r fr ml
                [DTag 0 (DInt (Z.of_nat (S j)))] kv0
                n0 tr0 ca0 j0 fl0 fd0 nf0 sc' lg0 (Z.of_nat (S (S j)))
                Hml Hr1 Hr2 Htbl) as (kv1 & Hrun).
    rewrite Hrun.
    destruct (IH tbl fr ml m' (S j) kv1
                n0 tr0 ca0 j0 fl0 fd0 nf0
                (lg0 ++ [(Z.of_nat (S j), (r, http_response tbl r))])
                Hml ltac:(lia) Hs' Htbl) as (kv2 & Hrun2).
    exists kv2.
    rewrite Hrun2.
    cbn [elog].
    rewrite <- app_assoc. cbn [app].
    replace (S j + List.length (r :: sc'))%nat
      with (S (S j) + List.length sc')%nat by (cbn [List.length]; lia).
    reflexivity.
Qed.

(* ===== §8  THE SERVER THEOREM (adr-0018 §6) ================================= *)

(** For EVERY route table, EVERY connection script, and fuels covering them: the
    transcript is exactly the spec — connection ids in accept order, each input
    preserved, each output the reference response function of its request.
    Unconditional beyond the stated size bounds; chunk size [ml] is universally
    quantified (chunking is unobservable, the adr-0017 principle carried to the
    socket layer). *)
Theorem http_prog_correct : forall tbl script fc fr ml,
  1 <= ml ->
  (List.length script <= fc)%nat ->
  Forall (fun r => (length r <= fr * Z.to_nat ml)%nat
                   /\ Z.of_nat (length r) <= int64_max) script ->
  Forall (fun qb => Z.of_nat (length (snd qb)) <= int64_max) tbl ->
  observe_sock (encode_table tbl) script (http_prog fc fr ml)
  = (ORet DUnit, expected_log tbl script).
Proof.
  intros tbl script fc fr ml Hml Hfc Hs Htbl.
  unfold observe_sock, run_sock, http_prog.
  rewrite run_repeat_eq.
  destruct (http_accept_loop tbl fr ml script fc 0
              (M.empty entry) 0 [] (M.empty dval) []
              (M.empty (list ascii)) [] 3 []
              Hml Hfc Hs Htbl) as (kv' & Hrun).
  change (Z.of_nat 1) with 1 in Hrun.
  rewrite Hrun.
  reflexivity.
Qed.

(* ===== §9  Anti-vacuity (adr-0005) ========================================== *)

(** MUTANT response function: Content-Length off by one — rejected on the smoke
    hit (the theorem instance is violated observably). *)
Definition http_response_mutant (tbl : list (list ascii * list ascii))
    (req : list ascii) : list ascii :=
  match find_sub crlf req with
  | None   => resp_400
  | Some i =>
      let line := firstn i req in
      if (4 <=? length line)%nat then
        if ascii_list_eqb (firstn 4 line) get_sp then
          let rest := skipn 4 line in
          match find_sub sp1 rest with
          | None   => resp_400
          | Some j =>
              match route_lookup tbl (firstn j rest) with
              | Some b =>
                  resp200_pre
                  ++ digits_of (Z.of_nat (S (length b)))    (* MUTANT: +1 *)
                  ++ crlfcrlf ++ b
              | None   => resp_404
              end
          end
        else resp_400
      else resp_400
  end.

Theorem response_mutant_rejected :
  http_response_mutant tb req_ok <> http_response tb req_ok.
Proof. vm_compute. intro H; discriminate H. Qed.

(** ... and plausible on misses (404s carry no length that varies). *)
Theorem response_mutant_plausible :
  http_response_mutant tb req_404 = http_response tb req_404.
Proof. vm_compute. reflexivity. Qed.

(** Inhabitance: the smoke scripts satisfy every hypothesis of the theorem — the
    general statement really covers the executed instances. *)
Theorem http_hyps_inhabited :
  1 <= 7
  /\ (List.length [req_ok; req_404; req_bad] <= 3)%nat
  /\ Forall (fun r => (length r <= 8 * Z.to_nat 7)%nat
                      /\ Z.of_nat (length r) <= int64_max)
       [req_ok; req_404; req_bad]
  /\ Forall (fun qb => Z.of_nat (length (snd qb)) <= int64_max) tb.
Proof.
  repeat split; try lia; repeat constructor; vm_compute; try discriminate; lia.
Qed.

(* ===== §9  Print Assumptions ================================================ *)
Print Assumptions sock_smoke.
Print Assumptions sock_smoke_straddle.
Print Assumptions sock_smoke_exhausted.
Print Assumptions http_route_correct.
Print Assumptions http_parse_correct.
Print Assumptions http_handle_correct.
Print Assumptions http_prog_correct.
Print Assumptions response_mutant_rejected.
Print Assumptions response_mutant_plausible.
Print Assumptions http_hyps_inhabited.
