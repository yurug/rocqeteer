(** * Gallery — time: [ONow]

    A run executes at a single injected instant: [ONow] returns it, and store
    liveness is judged against it. The clock is a parameter of [run_top] — the
    reference semantics never reads a wall clock, which is what makes
    replay/differential testing deterministic (and lets a consumer pin the
    instant per journal entry on recovery).

    Deep dive: theories/TimeStore.v (the observable), the Journal replay
    story in theories/Journal.v. *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

Definition k : list ascii := list_ascii_of_string "token".

Theorem now_is_the_injected_instant :
  let '(o, _) := run_top DUnit 1234 (Perform ONow []) in
  o = ORet (DInt 1234).
Proof. vm_compute. reflexivity. Qed.

(** The idiomatic TTL computation: read now, add the ttl with the CHECKED
    prim (overflow yields DNone, not garbage), set the deadline. *)
Definition put_with_ttl (ttl : Z) : tm :=
  Bind (Perform OPut [VBytes k; VInt 1])
  (Bind (Perform ONow [])
  (Bind (Prim PAddChecked [VVar 0; VInt ttl])
        (Match (VVar 0)
          [(PSome, Bind (Perform OSetDeadline [VBytes k; VSome (VVar 0)])
                        (Perform OGetDeadline [VBytes k]))]
          (Perform OThrow [VBytes (list_ascii_of_string "ttl overflow")])))).

Theorem ttl_lands_at_now_plus :
  let '(o, _) := run_top DUnit 1000 (put_with_ttl 500) in
  o = ORet (DSome (DSome (DInt 1500))).
Proof. vm_compute. reflexivity. Qed.
