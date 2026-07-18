(** * Gallery — observability: [OTrace]

    [OTrace v] appends a structured value to an append-only log and returns
    unit. The log is part of the observable ([observe] returns it in emission
    order), so "the program logged the right things, in the right order" is a
    provable statement — and the codegen realizes it as an OCaml effect.

    Deep dive: theories/Trace.v; trace-order-under-Fold in theories/Fold.v. *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

Definition k : list ascii := list_ascii_of_string "k".

(** Trace entries surface in emission order and interleave with real work. *)
Definition audited_write : tm :=
  Bind (Perform OTrace [VBytes (list_ascii_of_string "before")])
  (Bind (Perform OPut [VBytes k; VInt 5])
  (Bind (Perform OTrace [VPair (VBytes (list_ascii_of_string "wrote")) (VInt 5)])
        (Perform OGet [VBytes k]))).

Theorem trace_in_order :
  let '(o, _, tr) := observe DUnit 0 audited_write in
  o = ORet (DSome (DInt 5)) /\
  tr = [DBytes (list_ascii_of_string "before");
        DPair (DBytes (list_ascii_of_string "wrote")) (DInt 5)].
Proof. vm_compute. split; reflexivity. Qed.
