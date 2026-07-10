---
id: effir
type: spec
summary: EffIR is a first-order, de-Bruijn, two-layer (pure val / effectful tm) typed term language; this file pins its v2-R2 grammar, typing, and what is in and out of scope.
domain: spec
last-updated: 2026-07-10
depends-on: [adr-0001-first-order-ast, effect-signatures, adr-0008-general-match]
refines: []
related: [reference-semantics, codegen, error-taxonomy]
---
# Spec — EffIR (the first-order effect IR)

> ⚠ **Slice-1 status:** the built subset differs — `VZero`/`VSucc` instead of `VPrim (list val)`,
> no `typecheck_ir.ml`. IR v2 R2 (2026-07-10): general `Match` is implemented; `MatchOpt`
> is removed. See [[adr-0008-general-match]].

## One-liner
EffIR is the single first-order, explicit-binder representation that the reference interpreter evaluates
and the codegen lowers. Pure expressions (`val`) are separated from effectful computations (`tm`) so the
interpreter is total and the codegen is a direct syntactic translation.

## Scope
The v1 grammar, typing rules, binding discipline, and the in/out-of-scope construct list. The exact Rocq
constructor names are finalized during slice-1 implementation; this file fixes the **shape and invariants**
they must satisfy. Lowering to OCaml is in [[codegen]]; running in Rocq is in [[reference-semantics]].

## Types (`ty`)
```
ty ::= TUnit | TBool | TInt          (* TInt is zarith Z by default; see ADR-0004 / C4 *)
     | TOption ty | TPair ty ty
     | TNamed string                 (* abstract types realized via the manifest, e.g. "key","value","bytes" *)
```
Function types are **not** first-class values in v1: top-level definitions take a fixed arity of value
arguments and return a `tm`. No closures in EffIR values. (Keeps extraction simple — [[adr-0002-extraction-bridge]].)

## Pure expressions (`val`) — no effects, always terminating
```
val ::= VVar n                       (* de Bruijn index into the binder context *)
      | VUnit | VBool b
      | VInt z                       (* z : Z *)
      | VNone | VSome val
      | VPair val val
      | VBytes (list ascii)          (* binary byte string; evals to DBytes (IR v2 R1, 2026-07-10) *)
      | VPrim prim (list val)        (* call a registered PURE native realizer, e.g. value_succ, value_zero *)
```
`prim` names resolve through the runtime manifest ([[runtime-manifest]]); an unregistered prim is a codegen
error ([[error-taxonomy]]).

## Effectful computations (`tm`)
```
tm ::= Ret val                       (* pure result *)
     | Bind tm tm                     (* x <- t1 ;; t2 ; t2's context has one extra binder (de Bruijn 0 = x) *)
     | Perform op (list val)          (* trigger an effect operation with value arguments *)
     | Match val (list (pat * tm)) tm (* depth-1 general match: scrutinee, ordered branches, mandatory default *)
     | Repeat nat tm                  (* bounded loop: run body n times *)
```
`op` references an operation of a declared effect signature ([[effect-signatures]]); its argument and
return types are fixed by that declaration.

### Patterns (`pat`) — IR v2 R2 (adr-0008-general-match)
```
pat ::= PUnit | PBool b | PInt z | PBytes bs   (* literals — 0 binders, matched by equality *)
      | PNone                                   (* 0 binders *)
      | PSome                                   (* 1 binder: de Bruijn 0 = payload *)
      | PPair                                   (* 2 binders: db0 = second component, db1 = first component *)
```
Semantics: evaluate the scrutinee; try branches in order (**first-match-wins**); the first matching
branch runs its body with bound payloads pushed left-to-right (last payload = de Bruijn 0); the
**mandatory default arm** runs on no match, making Match total without a typechecker.

Binder convention for PPair: `match_pat PPair (DPair a b) = Some [a; b]`; `push_env` pushes `[a; b]`
left-to-right, so db0 = b (second, last pushed), db1 = a (first).

No nesting of patterns; no PVar/PWild (the default arm covers wildcards).
Match need not be exhaustive — the default arm handles all unmatched cases.

## Binding discipline
De Bruijn indices throughout. `Bind t1 t2` extends the context by one for `t2`. `Match` branches extend the
context by the pattern's bound-variable count. A surface notation layer may present named variables; it
elaborates to de Bruijn before anything else runs. Well-scopedness (every `VVar n` has `n < |context|`) is
a typechecker invariant.

## Typing (sketch)
Judgements `Γ ⊢ v : ty` (pure) and `Γ ⊢ t ÷ ty ! E` (computation of result type `ty`, effects in signature
`E`). Highlights:
- `Bind`: `Γ ⊢ t1 ÷ a ! E` and `Γ,a ⊢ t2 ÷ b ! E` ⇒ `Γ ⊢ Bind t1 t2 ÷ b ! E`.
- `Perform op vs`: `op` declared in `E` with arg types `as` and return `r`, `Γ ⊢ vs : as` ⇒ result `r`.
- `Match`: scrutinee type drives the required, exhaustive branch set; all branches share result type/effects.
The IR typechecker (`codegen/typecheck_ir.ml`) enforces arities, return types, scope, and exhaustiveness
**before** emission; failure is a codegen error, never a silent cast.

## In scope (v1)
`Ret`/`Bind`/`Perform`/`Match`; the value forms above; registered pure prims; a single effect or an
explicit sum of effects ([[effect-signatures]]); top-level non-recursive definitions (slice 1). Recursion
(structural / bounded-int / fuel) is added **after** the KV slice is green — see [[adr-0006-vertical-slice]].

## Out of scope (v1) — codegen MUST fail loudly (report §7.5)
First-class functions/closures in `val`; higher-order effect operations; dependent matches that would need
casts; cofixpoints; multi-shot continuations; well-founded recursion without compiled fuel/measure; calls
to unregistered prims/effects. A failed codegen beats an unsound one.

## Agent notes
> The `val`/`tm` split is deliberate and load-bearing: it keeps the reference interpreter **structurally
> recursive and total** (no effects hide inside a "pure" position) and makes `Bind` the *only* place a
> continuation lives — as a sub-term, not a closure. Do not collapse `val` and `tm` into one `expr`.

## Related files
- `spec/effect-signatures.md` — how `op`s and effect sums are declared and typed.
- `spec/reference-semantics.md` — the interpreter over `tm`.
- `spec/codegen.md` — the syntactic lowering of each `val`/`tm` form to OCaml.
</content>
