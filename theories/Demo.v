(** * Demo — the "audited counter" [demo_prog] proven correct.

    [demo_prog] (theories/Samples.v) composes Env + Trace + recursion + KV. This file proves
    its full functional result for a concrete run: from audit tag 99, the hit-counter at key
    0 ends at 3, the tag is persisted at key 9, and the trace records the tag. Because the run
    is closed (a concrete initial world), the proof is a single [vm_compute] — the GENERAL
    loop invariant (any [n]) is the inductive proof in theories/Recur.v. Run end-to-end by
    `make demo`. *)

From Stdlib Require Import ZArith List.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

Theorem demo_correct :
  let '(_, w) := run [] demo_prog (init_world (DInt 99)) in
     M.find 0 w.(kv) = Some (DInt 3)          (* counter bumped 3 times *)
  /\ M.find 9 w.(kv) = Some (DInt 99)          (* audit tag persisted *)
  /\ rev w.(trace) = [DInt 99].                (* trace recorded the tag *)
Proof. vm_compute. repeat split. Qed.

Print Assumptions demo_correct.
