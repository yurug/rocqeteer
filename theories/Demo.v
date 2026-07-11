(** * Demo — the "audited counter" [demo_prog] proven correct.

    [demo_prog] (theories/Samples.v) composes Env + Trace + recursion + KV. This file proves
    its full functional result for a concrete run: from audit tag 99, the hit-counter at key
    "0" ends at 3, the tag is persisted at key "9", and the trace records the tag. Because
    the run is closed (a concrete initial world, instant now = 0), the proof is a single
    [vm_compute] — the GENERAL loop invariant (any [n]) is the inductive proof in
    theories/Recur.v. Run end-to-end by `make demo`.

    R4 (adr-0011): keys are decimal byte strings; entries carry (value, optional deadline)
    — [demo_prog] writes deadline-less entries only. *)

From Stdlib Require Import ZArith List String Ascii.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

Theorem demo_correct :
  let '(_, w) := run [] demo_prog (init_world (DInt 99) 0) in
     M.find (string_of_list_ascii key0) w.(kv) = Some (DInt 3, None)   (* counter bumped 3× *)
  /\ M.find (string_of_list_ascii key9) w.(kv) = Some (DInt 99, None)  (* audit tag persisted *)
  /\ rev w.(trace) = [DInt 99].                                        (* trace recorded the tag *)
Proof. vm_compute. repeat split. Qed.

Print Assumptions demo_correct.
