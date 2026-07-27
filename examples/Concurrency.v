(** * Gallery — concurrency: [OSpawn] · [OYield] · [OChanMake] · [OChanSend] · [OChanRecv]  (C5, adr-0019)

    Cooperative fibers over ONE shared world, with a SCHEDULE ORACLE: the
    interleaving is an injected [list fiber_id] (the C4 connection-script pattern
    generalized from content to scheduling order), so a run is a deterministic
    FUNCTION of its schedule.  Channels are the only sharing — no shared-memory op,
    so DATA RACES ARE NOT REPRESENTABLE — and deadlock is a modeled VALUE, never a
    hang.

    A suspended fiber is first-order: a defunctionalized continuation over the SAME
    [tm] (the CEK step machine, [theories/Cek.v]), proven to AGREE with big-step
    [run] on the concurrency-free fragment ([Cek.cek_adequate]).  The scheduler is
    [theories/Sched.v]; the sample fibers reused below (fA/fB, fProd/fCons, fD1/fD2)
    and their initial states (s_int/s_pc/s_dead) are its anti-vacuity witnesses.

    The flagship is [SchedHttp.drv_concurrent_matches]: a genuinely concurrent
    acceptor+worker server, scheduled run-to-completion, serves EXACTLY the proven
    SEQUENTIAL transcript ([SockIO.http_prog_correct]).  tests/diff_sched.ml replays
    schedules against the extracted [run_sched], and tools/rhttpd_conc runs the same
    fibers over REAL TCP via the OCaml [Effect.Deep] scheduler realizer. *)
From Stdlib Require Import ZArith List Ascii.
From Rocqeteer Require Import EffIR Samples Sched.
From RocqeteerApps Require Import SockIO SchedHttp.
Import ListNotations.
Local Open Scope Z_scope.

(** Fiber A traces 10, YIELDS, traces 11; fiber B traces 20.  The schedule decides
    where B lands — [1;2;1] interleaves it BETWEEN A's halves... *)
Theorem interleave_B_between :
  rev (trace (swld (run_sched nb [1; 2; 1] s_int))) = [DInt 10; DInt 20; DInt 11].
Proof. vm_compute. reflexivity. Qed.

(** ...while [1;1;2] runs A to completion FIRST.  Same fibers, different trace: the
    oracle genuinely controls the observable (no interleaving is baked in). *)
Theorem interleave_B_after :
  rev (trace (swld (run_sched nb [1; 1; 2] s_int))) = [DInt 10; DInt 11; DInt 20].
Proof. vm_compute. reflexivity. Qed.

Theorem schedule_is_load_bearing :
  trace (swld (run_sched nb [1; 2; 1] s_int))
  <> trace (swld (run_sched nb [1; 1; 2] s_int)).
Proof. vm_compute. intro H; discriminate H. Qed.

(** Channel hand-off across fibers: the producer sends 42 on channel 0, the consumer
    receives it and traces it — and both fibers complete. *)
Theorem channel_handoff :
  rev (trace (swld (run_sched nb [1; 2; 2; 1] s_pc))) = [DInt 42]
  /\ sfib (run_sched nb [1; 2; 2; 1] s_pc) = [].
Proof. split; vm_compute; reflexivity. Qed.

(** Deadlock is a VALUE, not a hang: two fibers each block on the other's empty
    channel; every schedule leaves both live, reported as [Stuck]. *)
Theorem deadlock_is_a_value :
  sresult_of (run_sched nb [1; 2; 1; 2] s_dead) = Stuck [1; 2] [].
Proof. vm_compute. reflexivity. Qed.

(** THE flagship: the certified CONCURRENT HTTP server — an acceptor fiber and a
    worker fiber over a channel — serves, under a run-to-completion schedule, EXACTLY
    the proven sequential transcript (a hit, a miss, a malformed request). *)
Theorem concurrent_server_matches_sequential :
  conn_log (swld (run_sched nb drv_sched (drv_init tb sc3 3 3 8 7)))
  = expected_log tb sc3.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions interleave_B_between.
Print Assumptions schedule_is_load_bearing.
Print Assumptions channel_handoff.
Print Assumptions deadlock_is_a_value.
Print Assumptions concurrent_server_matches_sequential.
