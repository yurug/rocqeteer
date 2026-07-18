(** * Gallery — expiring bindings: [OSetDeadline] / [OGetDeadline]

    Every store binding carries an optional deadline; a binding is LIVE at
    instant [now] iff [now <= deadline]. Expired bindings are semantically
    absent from every store op — no separate "expired" state exists.

    Deep dive (the liveness boundary both ways, oracle-validated; general
    lemmas): theories/TimeStore.v, theories/StoreAssert.v. *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

Definition k : list ascii := list_ascii_of_string "session".

(** put; expire at t=500; read back the deadline. *)
Definition set_ttl : tm :=
  Bind (Perform OPut [VBytes k; VInt 1])
  (Bind (Perform OSetDeadline [VBytes k; VSome (VInt 500)])
        (Perform OGetDeadline [VBytes k])).

Theorem deadline_reads_back :
  let '(o, _) := run_top DUnit 0 set_ttl in
  o = ORet (DSome (DSome (DInt 500))).
Proof. vm_compute. reflexivity. Qed.

(** The boundary, both faces: alive AT the deadline... *)
Definition get_at (now : Z) : outcome :=
  fst (run_top DUnit now
        (Bind (Perform OPut [VBytes k; VInt 7])
         (Bind (Perform OSetDeadline [VBytes k; VSome (VInt 500)])
               (Perform OGet [VBytes k])))).

Theorem alive_at_the_deadline : get_at 500 = ORet (DSome (DInt 7)).
Proof. vm_compute. reflexivity. Qed.

(** ...and gone one instant past it. (The put/set run at [now] too; what
    matters is the final read at 501 > 500.) *)
Theorem gone_one_past_it : get_at 501 = ORet DNone.
Proof. vm_compute. reflexivity. Qed.

(** [VNone] clears a deadline (PERSIST). *)
Theorem persist_clears :
  let '(o, _) := run_top DUnit 0
    (Bind (Perform OPut [VBytes k; VInt 1])
     (Bind (Perform OSetDeadline [VBytes k; VSome (VInt 500)])
      (Bind (Perform OSetDeadline [VBytes k; VNone])
            (Perform OGetDeadline [VBytes k])))) in
  o = ORet (DSome DNone).
Proof. vm_compute. reflexivity. Qed.
