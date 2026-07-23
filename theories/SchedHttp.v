(** * SchedHttp — C5 (adr-0019): the concurrent HTTP driver ↔ the certified server.

    The pay-off of the C5 machinery: the SAME proven sequential HTTP server
    (SockIO.http_prog_correct) run UNDER the cooperative scheduler recovers its exact
    transcript — first as one scheduled fiber (general, by law), then as a genuinely
    CONCURRENT acceptor+worker structure under a run-to-completion schedule (concrete).

    §A  THE GENERAL RECOVERY.  [http_prog] is concurrency-free, so [conc_free_embeds]
    /[seq_embedding_cf] discharge the machine-interface obligation with NO hypothesis:
    a single fiber running [http_prog] embeds into [run_sched] as big-step [run], and
    [http_prog_correct] then pins the transcript to [expected_log].  General over every
    route table and connection script (adr-0019 §Decision: "sequential semantics under
    the singleton schedule").  The only side condition is the fixed per-fiber fuel
    budget [RTS_FUEL] — every closed program meets it (discharged by [vm_compute] in the
    smoke corollary; unboundedly by [conc_free_embeds]).

    §B  THE CONCURRENT DRIVER (concrete).  A real two-fiber structure — an ACCEPTOR that
    [OAccept]s and hands each connection to a WORKER over a channel ([OChanSend]/
    [OChanRecv], the idiomatic Eio worker-pool) — produces, under a run-to-completion
    schedule, the EXACT [expected_log].  Genuinely uses [OSpawn]-class concurrency ops
    (channels), yet observationally equals the sequential server.  Anti-vacuity: a
    schedule that never runs the worker produces NO transcript — the schedule oracle
    genuinely controls the outcome.

    Re-deriving §A's transcript through the multi-fiber channel plumbing GENERALLY (not
    just at the smoke instance) is the statement-boundary reserved in the plan; §B pins
    the concrete witness, §A gives the general law for the single-fiber embedding. *)

From Stdlib Require Import List ZArith Ascii Lia.
From Rocqeteer Require Import EffIR Cek Sched Samples SockIO.
Import ListNotations.
Local Open Scope Z_scope.

Local Notation length := List.length.

(* ===== §0  The socket-initial world (mirrors [run_sock]) ==================== *)

Definition sockw (tbl : list (list ascii * list ascii)) (sc : list (list ascii))
  : world :=
  mkWorld (M.empty entry) (encode_table tbl) 0 [] (M.empty dval) []
          (M.empty (list ascii)) [] 3 sc [] [] 1.

Lemma run_sock_sockw : forall tbl sc t,
  run_sock (encode_table tbl) sc t = run [] t (sockw tbl sc).
Proof. reflexivity. Qed.

(** [http_prog] performs only store/socket ops — never a concurrency op — so it is
    concurrency-free for every fuel/chunk parameter. *)
Lemma conc_free_http_prog : forall fc fr ml, conc_free (http_prog fc fr ml).
Proof. intros fc fr ml; cbn; repeat split; reflexivity. Qed.

(* ===== §A  General recovery: the certified server as a scheduled fiber ====== *)

(** The proven sequential server, run as ONE scheduled fiber, recovers its exact
    transcript: [conn_log] = [expected_log], the fiber completes [ORet DUnit], nothing
    remains.  [http_prog_correct] transferred through the scheduler by the conc-free
    embedding — no interpreter re-proof, the oracle is preserved verbatim. *)
Theorem http_driver_seq : forall tbl script fc fr ml fid nf nc,
  1 <= ml ->
  (length script <= fc)%nat ->
  Forall (fun r => (length r <= fr * Z.to_nat ml)%nat
                   /\ Z.of_nat (length r) <= int64_max) script ->
  Forall (fun qb => Z.of_nat (length (snd qb)) <= int64_max) tbl ->
  (exists n, (n <= RTS_FUEL)%nat
             /\ fdone (fst (run_to_sched n
                             (FE (http_prog fc fr ml) [] []) (sockw tbl script)))
                = true) ->
  let s := run_sched nb [fid]
             (init_sst (sockw tbl script)
                [(fid, FE (http_prog fc fr ml) [] [])] [] nf nc) in
  conn_log (swld s) = expected_log tbl script
  /\ sdone s = [(fid, ORet DUnit)]
  /\ sfib s = [].
Proof.
  intros tbl script fc fr ml fid nf nc Hml Hfc Hs Htbl Hfuel. cbn zeta.
  pose proof (http_prog_correct tbl script fc fr ml Hml Hfc Hs Htbl) as Hcorr.
  unfold observe_sock in Hcorr. rewrite run_sock_sockw in Hcorr.
  destruct (run [] (http_prog fc fr ml) (sockw tbl script)) as [r w] eqn:Erun.
  cbn [fst snd] in Hcorr. injection Hcorr as Hr Hlog.
  destruct (seq_embedding_cf (http_prog fc fr ml) (sockw tbl script) fid nf nc
              (conc_free_http_prog fc fr ml) Hfuel) as (Hw & Hd & Hf).
  rewrite Erun in Hw, Hd; cbn [fst snd] in Hw, Hd.
  repeat split.
  - rewrite Hw; exact Hlog.
  - rewrite Hd, Hr; reflexivity.
  - exact Hf.
Qed.

(** The smoke instance: fuel budget discharged by [vm_compute], hypotheses by
    [http_hyps_inhabited]'s shape — a self-contained, hypothesis-free corollary that
    the certified server runs faithfully under the scheduler. *)
Theorem http_driver_seq_smoke :
  let s := run_sched nb [1]
             (init_sst (sockw tb [req_ok; req_404; req_bad])
                [(1, FE sample_http [] [])] [] 2 1) in
  conn_log (swld s) = expected_log tb [req_ok; req_404; req_bad]
  /\ sdone s = [(1, ORet DUnit)]
  /\ sfib s = [].
Proof.
  apply (http_driver_seq tb [req_ok; req_404; req_bad] 3 8 7 1 2 1).
  - lia.
  - cbn; lia.
  - repeat constructor; vm_compute; try discriminate; lia.
  - repeat constructor; vm_compute; discriminate.
  - exists RTS_FUEL. split; [apply Nat.le_refl | vm_compute; reflexivity].
Qed.

(* ===== §B  The concurrent driver: acceptor + worker over a channel ========= *)

(** ACCEPTOR: accept a connection, hand it (the whole [DTag] accept result at db0) to
    the worker over channel 0 — then loop.  [OChanSend] is the yield point. *)
Definition acceptor (fc : nat) : tm :=
  Repeat fc (Bind (Perform OAccept []) (Perform OChanSend [VInt 0; VVar 0])).

(** WORKER: receive a connection off channel 0 and run the SAME per-connection handler
    the sequential server uses (the accept-result [Match] arm) — then loop.  [OChanRecv]
    is the yield point; an empty channel BLOCKS (the schedule must feed it first). *)
Definition worker (fw fr : nat) (ml : Z) : tm :=
  Repeat fw (Bind (Perform OChanRecv [VInt 0])
               (Match (VVar 0) [(PTag 0, http_handle fr ml)] (Ret VUnit))).

(** Two fibers sharing the shared world and one pre-made channel (id 0). *)
Definition drv_init (tbl : list (list ascii * list ascii)) (sc : list (list ascii))
    (fc fw fr : nat) (ml : Z) : sst :=
  init_sst (sockw tbl sc)
    [(1, FE (acceptor fc) [] []); (2, FE (worker fw fr ml) [] [])]
    [(0, [])] 3 1.

Definition drv_sched : list Z := [1; 2; 1; 2; 1; 2; 1; 2].
Definition sc3 : list (list ascii) := [req_ok; req_404; req_bad].

(** THE concurrent-driver theorem: under the run-to-completion schedule, the two-fiber
    acceptor/worker structure produces EXACTLY the sequential server's transcript
    ([expected_log]) and both fibers complete.  Certified concurrency, scheduled
    run-to-completion, equals the proven sequential server — concretely. *)
Theorem drv_concurrent_matches :
  conn_log (swld (run_sched nb drv_sched (drv_init tb sc3 3 3 8 7)))
  = expected_log tb sc3
  /\ sfib (run_sched nb drv_sched (drv_init tb sc3 3 3 8 7)) = [].
Proof. split; vm_compute; reflexivity. Qed.

(** Anti-vacuity — the SCHEDULE is load-bearing: a schedule that never runs the worker
    (fiber 2) leaves the transcript EMPTY despite the acceptor accepting connections.
    The oracle genuinely controls the observable (cf. [Sched.schedule_matters]). *)
Theorem drv_worker_starved :
  conn_log (swld (run_sched nb [1; 1; 1; 1] (drv_init tb sc3 3 3 8 7))) = [].
Proof. vm_compute. reflexivity. Qed.

(* ===== §C  Print Assumptions ================================================ *)

(** Each must read "Closed under the global context". *)
Print Assumptions http_driver_seq.
Print Assumptions http_driver_seq_smoke.
Print Assumptions drv_concurrent_matches.
Print Assumptions drv_worker_starved.
