(** * Gallery — the keyed store: [OGet] / [OPut] / [ODelete]

    The State effect over a bytes-keyed store. [OPut k v] stores a value,
    [OGet k] returns [DSome v] for a live binding and [DNone] otherwise,
    [ODelete k] returns whether a live binding was removed.

    Deep dive (general theorems, frame clauses, mutants): theories/KV.v,
    theories/TimeStore.v. *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

Definition k : list ascii := list_ascii_of_string "counter".
Definition other : list ascii := list_ascii_of_string "other".

(** put; get — the value comes back. *)
Definition put_then_get : tm :=
  Bind (Perform OPut [VBytes k; VInt 42])
       (Perform OGet [VBytes k]).

Theorem put_then_get_returns_it :
  let '(o, _) := run_top DUnit 0 put_then_get in
  o = ORet (DSome (DInt 42)).
Proof. vm_compute. reflexivity. Qed.

(** ...and a different key is untouched (the frame, in one instance). *)
Theorem other_key_stays_absent :
  let '(o, _) := run_top DUnit 0 (Bind (Perform OPut [VBytes k; VInt 42])
                                       (Perform OGet [VBytes other])) in
  o = ORet DNone.
Proof. vm_compute. reflexivity. Qed.

(** delete reports whether it removed a live binding. *)
Definition put_delete_get : tm :=
  Bind (Perform OPut [VBytes k; VInt 1])
  (Bind (Perform ODelete [VBytes k])
        (Perform OGet [VBytes k])).

Theorem deleted_means_gone :
  let '(o, _) := run_top DUnit 0 put_delete_get in
  o = ORet DNone.
Proof. vm_compute. reflexivity. Qed.

Theorem delete_missing_is_false :
  let '(o, _) := run_top DUnit 0 (Perform ODelete [VBytes k]) in
  o = ORet (DBool false).
Proof. vm_compute. reflexivity. Qed.
