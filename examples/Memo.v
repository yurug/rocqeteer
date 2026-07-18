(** * Gallery — cache: [OCacheGet] / [OCachePut]

    A bytes-keyed memo table, DELIBERATELY invisible to [observe]: correctness
    statements cannot depend on cache state, which is exactly what makes
    "the cache is only an optimization" a structural property rather than a
    hope. [OCacheGet] returns [DSome v] / [DNone]; [OCachePut] overwrites.

    Deep dive: theories/Cache.v (cache-oblivious observables). *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

Definition ck : list ascii := list_ascii_of_string "memo:fib10".

(** Miss, fill, hit — the memoization skeleton. *)
Definition memoized : tm :=
  Bind (Perform OCacheGet [VBytes ck])
       (Match (VVar 0)
         [(PSome, Ret (VVar 0))]                       (* hit: reuse *)
         (Bind (Perform OCachePut [VBytes ck; VInt 55]) (* miss: compute+fill *)
               (Ret (VInt 55)))).

Theorem first_call_misses_and_fills :
  let '(o, _) := run_top DUnit 0 memoized in
  o = ORet (DInt 55).
Proof. vm_compute. reflexivity. Qed.

Theorem second_call_hits :
  let '(o, _) := run_top DUnit 0 (Bind memoized memoized) in
  o = ORet (DInt 55).
Proof. vm_compute. reflexivity. Qed.

(** The observable ignores the cache: a run that only touches the cache has
    an empty live store and an empty trace. *)
Theorem cache_is_invisible :
  let '(o, live, tr) := observe DUnit 0 (Perform OCachePut [VBytes ck; VInt 1]) in
  o = ORet DUnit /\ live = [] /\ tr = [].
Proof. vm_compute. repeat split. Qed.
