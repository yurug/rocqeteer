---
id: reference-semantics
type: spec
summary: The reference semantics is a pure, total Rocq interpreter of EffIR tm against a pure handler; it is the proof target and the differential-test oracle, and carries the Hoare/verifies layer.
domain: spec
last-updated: 2026-06-20
depends-on: [effir, effect-signatures]
refines: []
related: [codegen, conv-testing-strategy, adr-0004-trust-model, adr-0005-anti-vacuity]
---
# Spec — Reference semantics & the Hoare layer

## One-liner
A pure Rocq function `run` evaluates an EffIR `tm` by folding a pure per-operation handler over a state.
It is what proofs target and what differential tests treat as the oracle. The fast OCaml is asserted to
refine it (axiom, [[adr-0004-trust-model]]).

## Scope
The interpreter's shape and totality argument, the handler interface, the closed environment for pure
`val`s, the `Spec`/`verifies` Hoare layer, and the algebraic laws to establish. The OCaml side is in [[codegen]].

## Pure-value evaluation
`eval_val : env -> val -> result_value` interprets `val` in a closed environment (a list keyed by de Bruijn
index). It is total and effect-free: `VPrim p vs` calls the registered **pure** realizer for `p`. Reference
realizers are the *faithful math model* (e.g. `value` modeled with `Z`), independent of the fast runtime's
representation — divergence between them is exactly what differential testing hunts (overflow etc., [[conv-testing-strategy]]).

## Computation evaluation (handler-parameterized)
```coq
(* handler : forall A, op A -> state -> A * state   (pure, deterministic) *)
Fixpoint run {A} (h : Handler) (env : env) (t : tm) (s : state) : value * state := ...
  (* Ret v        => (eval_val env v, s)
     Perform op vs => h op (eval_val env <$> vs) s
     Bind t1 t2    => let (x,s') := run h env t1 s in run h (x::env) t2 s'
     Match v brs   => run h (extend env (selected branch's binders)) (branch body) s *)
```
**Totality:** `run` recurses only on structural sub-terms of `t` (slice 1 has no recursion in programs), so
it is a plain `Fixpoint`. When program-level recursion is added, it is via compiled fuel/measure ([[effir]]
out-of-scope list), keeping `run` structural. Runtime values are a `dval` sum
(`DUnit`/`DBool`/`DInt Z`/`DNone`/`DSome`/`DPair`/**`Dstuck`**); impossible or ill-typed cases yield `Dstuck`,
discharged as unreachable for well-typed closed terms. `run` is therefore **total** returning `dval * state`
(not `option`) — `verifies` below destructures a total pair (`plan.md` Resolution 2).

## KV reference handler (slice 1)
```coq
Definition handle_kv {A} (op : KV A) (s : map) : A * map :=
  match op with
  | Get k    => (find k s, s)
  | Put k v  => (tt, add k v s)
  | Delete k => (tt, remove k s)
  end.
```
`map` is a stdlib finite map (no external deps, [[adr-0003-dependency-budget]]). This handler is proven to
refine an abstract map model and is the oracle the OCaml `Hashtbl` handler is differentially tested against.

## Hoare / verifies layer
```coq
Record Spec (S A : Type) := { pre : S -> Prop; post : S -> A -> S -> Prop }.
Definition verifies (h:Handler)(t:tm)(sp:Spec state value) : Prop :=
  forall s, pre sp s -> let '(x,s') := run h [] t s in post sp s x s'.
```
Example obligation (KV): `verifies handle_kv (incr k) {| pre := fun _ => True;
post := fun s _ s' => find k s' = Some (value_succ (default value_zero (find k s))) |}`.

### Mandatory anti-vacuity companions ([[adr-0005-anti-vacuity]])
For every `verifies` theorem: (1) an **inhabitance lemma** `∃ s, pre sp s`; (2) a **proof-mutation test** —
a wrong `incr'` (e.g. one that `Put`s `value_zero`) for which the same spec must be **un**provable. A spec
with `pre := fun _ => False` or `post := fun _ _ _ => True` is rejected at review.

## Algebraic laws to establish (report §5.6)
State: `put k v ;; get k = put k v ;; ret (Some v)`, `put k v1 ;; put k v2 = put k v2`,
`get k ;; get k = get k`. Plus monad laws for `Bind`/`Ret` up to the interpreter's extensional equality.
These drive rewrites and are the Level-1 reasoning ([[prop-functional]]).

## Agent notes
> The reference interpreter and the codegen must consume the **same** EffIR value
> ([[adr-0002-extraction-bridge]]). Keep `run` pure and deterministic — any nondeterminism here destroys
> its value as an oracle. Reference realizers favor *faithfulness* (e.g. unbounded `Z`) over speed; speed
> is the fast side's job.

## Related files
- `spec/codegen.md` — the fast OCaml that must refine this.
- `conventions/testing-strategy.md` — how `run` is used as the differential oracle.
- `properties/functional.md` — the laws and refinement properties stated as P-entries.
</content>
