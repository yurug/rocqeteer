(** * Gallery — environment: [OAsk]

    [OAsk] returns the run's immutable context value (request arguments,
    configuration). It is the Reader effect: same [w.(ctx)] every time, no
    write form exists. Consumers pass one structured [dval] (typically a
    [DList] of arguments) and destructure it with [Match].

    Deep dive: theories/Env.v; argv-style folds over the context in
    theories/Fold.v. *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

(** Dispatch on the request: a program that answers depending on its context. *)
Definition greet : tm :=
  Bind (Perform OAsk [])
       (Match (VVar 0)
         [(PBytes (list_ascii_of_string "ping"),
             Ret (VBytes (list_ascii_of_string "pong")))]
         (Perform OThrow [VBytes (list_ascii_of_string "unknown command")])).

Theorem ping_gets_pong :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "ping")) 0 greet in
  o = ORet (DBytes (list_ascii_of_string "pong")).
Proof. vm_compute. reflexivity. Qed.

Theorem anything_else_errors :
  let '(o, _) := run_top (DBytes (list_ascii_of_string "quit")) 0 greet in
  o = OErr (DBytes (list_ascii_of_string "unknown command")).
Proof. vm_compute. reflexivity. Qed.

(** The context is stable: asking twice yields the same value. *)
Theorem ask_is_pure_reader :
  let '(o, _) := run_top (DInt 7) 0
    (Bind (Perform OAsk [])
     (Bind (Perform OAsk [])
           (Ret (VPair (VVar 1) (VVar 0))))) in
  o = ORet (DPair (DInt 7) (DInt 7)).
Proof. vm_compute. reflexivity. Qed.
