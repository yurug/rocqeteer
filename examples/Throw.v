(** * Gallery — errors: [OThrow]

    [OThrow e] aborts the run with payload [e]; [Bind] short-circuits, so the
    continuation never runs — but effects performed BEFORE the throw stay
    (no rollback: the semantics is exceptions, not transactions).

    Deep dive: theories/Error.v; throw payloads through Match arms in
    theories/Journal.v (pre-throw journal entries survive). *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

Definition k : list ascii := list_ascii_of_string "k".

(** The continuation after a throw is dead code. *)
Theorem throw_short_circuits :
  let '(o, _) := run_top DUnit 0
    (Bind (Perform OThrow [VBytes (list_ascii_of_string "boom")])
          (Perform OPut [VBytes k; VInt 1])) in
  o = OErr (DBytes (list_ascii_of_string "boom")).
Proof. vm_compute. reflexivity. Qed.

(** ...but effects before the throw are committed: the put below lands even
    though the run aborts. [observe] shows the store despite the error. *)
Theorem pre_throw_effects_stay :
  let '(o, live, _) := observe DUnit 0
    (Bind (Perform OPut [VBytes k; VInt 1])
          (Perform OThrow [VInt 99])) in
  o = OErr (DInt 99) /\ live <> [].
Proof. vm_compute. split. reflexivity. congruence. Qed.

(** Payloads are structured values, not strings: a tagged error with data. *)
Theorem structured_error_payload :
  let '(o, _) := run_top DUnit 0
    (Perform OThrow [VPair (VBytes (list_ascii_of_string "wrongtype")) (VInt 3)]) in
  o = OErr (DPair (DBytes (list_ascii_of_string "wrongtype")) (DInt 3)).
Proof. vm_compute. reflexivity. Qed.
