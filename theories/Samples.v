(** Sample EffIR programs that exercise codegen/runtime paths [prog0] does not:
    [ODelete], a top-level [Ret], multiple [Perform]s to distinct keys, a negative key
    literal, and depth-2 de Bruijn nesting. Consumed by the multi-program differential
    test (audit finding 1) so those lowering rules are covered, not dead. All are slice-1
    typed (key = value = Z; values via VInt/VZero/VSucc). *)

From Stdlib Require Import ZArith List String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

(** get 2; if absent put 1, else DELETE 2 — exercises [ODelete]. *)
Definition sample_delete : tm :=
  Bind (Perform OGet [VInt 2])
       (MatchOpt (VVar 0)
          (Perform OPut [VInt 2; VSucc VZero])
          (Perform ODelete [VInt 2])).

(** put 3 := 1 ; put 4 := 2 — two sequential Performs to distinct keys. *)
Definition sample_two : tm :=
  Bind (Perform OPut [VInt 3; VSucc VZero])
       (Perform OPut [VInt 4; VSucc (VSucc VZero)]).

(** get 6 ; return it — a top-level [Ret] of a bound variable; state unchanged. *)
Definition sample_ret : tm :=
  Bind (Perform OGet [VInt 6]) (Ret (VVar 0)).

(** increment at a NEGATIVE key — exercises negative-literal lowering. *)
Definition sample_neg : tm := incr_at (-3).

(** depth-2 nesting: get 8; get 9; match the FIRST result (de Bruijn index 1, under the
    second binder) — exercises de Bruijn shifting the single-Bind prog0 never reaches. *)
Definition sample_nested : tm :=
  Bind (Perform OGet [VInt 8])
       (Bind (Perform OGet [VInt 9])
             (MatchOpt (VVar 1)
                (Perform OPut [VInt 8; VSucc VZero])
                (Perform OPut [VInt 8; VSucc (VVar 0)]))).

(** ERROR effect: put 1 := 1; THROW 99; put 2 := 2 — the throw aborts, so the second put
    never runs and the state keeps only the pre-throw write. *)
Definition sample_throw : tm :=
  Bind (Perform OPut [VInt 1; VSucc VZero])
       (Bind (Perform OThrow [VInt 99])
             (Perform OPut [VInt 2; VSucc (VSucc VZero)])).

(** ERROR + KV composed: get 5; if absent THROW 7, else increment — one path returns
    normally, the other aborts, so a random state exercises both. *)
Definition sample_guard5 : tm :=
  Bind (Perform OGet [VInt 5])
       (MatchOpt (VVar 0)
          (Perform OThrow [VInt 7])
          (Perform OPut [VInt 5; VSucc (VVar 0)])).

(** ENV + KV composed: read the read-only context, then store it at key 1 — exercises
    [OAsk] and that the asked value flows into a Put. *)
Definition sample_env : tm :=
  Bind (Perform OAsk [])
       (Perform OPut [VInt 1; VVar 0]).

(** TRACE + KV composed: emit 10; put 1 := 1; emit 20 — the trace must record [10; 20] in
    order, and the put must commit, exercising [OTrace] interleaved with KV. *)
Definition sample_trace : tm :=
  Bind (Perform OTrace [VInt 10])
       (Bind (Perform OPut [VInt 1; VSucc VZero])
             (Perform OTrace [VInt 20])).

(** CACHE + KV composed (memoize): look up key 0 in the cache; on a HIT store the cached
    value at key 1, on a MISS compute [succ zero]=1, cache it at 0, and store it at key 1.
    The KV result (key 1) is the same whether the cache hits or misses with the correct
    value — that observational invisibility is what [theories/Cache.v] proves. *)
Definition sample_cache : tm :=
  Bind (Perform OCacheGet [VInt 0])
       (MatchOpt (VVar 0)
          (Bind (Perform OCachePut [VInt 0; VSucc VZero])
                (Perform OPut [VInt 1; VSucc VZero]))
          (Perform OPut [VInt 1; VVar 0])).

(** RECURSION: increment key 0 five times via a bounded loop — exercises [Repeat]. After
    [n] iterations from empty, key 0 holds [n] (proven by induction in theories/Recur.v). *)
Definition sample_count : tm := Repeat 5 (incr_at 0).

(** SINGLE SOURCE OF TRUTH for the program list. The codegen iterates this (so it emits one
    [let name () = …] per entry), and extraction of it pulls every referenced sample as a
    named value. Adding a program is THEN a one-line edit here — no separate codegen or
    extraction list to keep in sync (kb/spec/codegen.md; tooling iteration). *)
Definition all_programs : list (string * tm) :=
  [ ("prog0"%string, prog0);
    ("sample_delete"%string, sample_delete);
    ("sample_two"%string, sample_two);
    ("sample_ret"%string, sample_ret);
    ("sample_neg"%string, sample_neg);
    ("sample_nested"%string, sample_nested);
    ("sample_throw"%string, sample_throw);
    ("sample_guard5"%string, sample_guard5);
    ("sample_env"%string, sample_env);
    ("sample_trace"%string, sample_trace);
    ("sample_cache"%string, sample_cache);
    ("sample_count"%string, sample_count) ].
