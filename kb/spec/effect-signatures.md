---
id: effect-signatures
type: spec
summary: An effect signature is a type-indexed family of operations declared in Rocq, mirrored 1:1 by an OCaml extensible-effect declaration; KV is the slice-1 signature, and effects compose by explicit sum.
domain: spec
last-updated: 2026-06-20
depends-on: [effir]
refines: []
related: [reference-semantics, codegen, ext-ocaml5-effects]
---
# Spec — Effect signatures

## One-liner
An effect signature names a set of operations, each with fixed argument types and a fixed result type. The
result type being part of the operation is what makes typed codegen and typed OCaml handlers possible.

## Scope
How effects are declared in Rocq, how `Perform` references them, how the same signature maps to OCaml's
`type _ Effect.t += …`, and how multiple effects compose in v1. The KV signature is the slice-1 example.

## Rocq shape
A signature is a `Variant E : Type -> Type` whose constructors are the operations; the index is the result type.
```coq
Variant KV : Type -> Type :=
| Get    : key -> KV (option value)
| Put    : key -> value -> KV unit
| Delete : key -> KV unit.
```
In EffIR, an operation is referenced by `(effect_name, op_name)` with its declared arg `ty`s and result
`ty`; `Perform (KV,Get) [k]` is well-typed iff `k : TNamed "key"` and yields `TOption (TNamed "value")`.
See [[effir]].

## OCaml mirror (generated)
Each signature maps 1:1 to an extensible-variant extension plus thin `perform` wrappers:
```ocaml
type _ Effect.t +=
  | Get    : key -> value option Effect.t
  | Put    : key * value -> unit Effect.t
  | Delete : key -> unit Effect.t
(* val get : key -> value option = fun k -> Effect.perform (Get k)  (etc.) *)
```
Constructors are kept private behind the module signature; client/generated code calls `get`/`put`/`delete`,
not raw `Effect.perform` ([[ext-ocaml5-effects]], and the CI rule banning stray `perform`). The handler
that interprets them lives in `runtime/` and is placed at a stable region boundary ([[codegen]] §handlers).

## Operation result types (typed codegen hinge)
The result type in the constructor is authoritative end-to-end: it drives the EffIR typechecker, the OCaml
`Effect.t` index, and the handler's `continue kcont (v : result)` type. A mismatch is a type error in OCaml
(loud), not a runtime cast.

## Composing effects (v1)
v1 uses **explicit sums**, not a typeclass/row-polymorphic injection:
```coq
Variant SumE (E F : Type -> Type) : Type -> Type :=
| Inl : forall A, E A -> SumE E F A
| Inr : forall A, F A -> SumE E F A.
```
Verbose but transparent — the generator emits predictable constructors and the handler nesting order is
explicit. A typeclass-based `SubEff` injection is a possible later ergonomic layer, not v1.

## Slice-1 signature: KV
`Get`/`Put`/`Delete` over abstract `key`/`value` (`TNamed`), realized via the manifest. Slice 1 keeps
`key`/`value` abstract; arithmetic in `incr` uses pure prims `value_zero`/`value_succ` (registered prims, [[runtime-manifest]]).

## Agent notes
> Resist row-polymorphic/extensible-effect cleverness in v1 (the report warns against it too). Explicit
> sums keep the OCaml output reviewable and the handler order unambiguous — which is itself a trust property.

## Related files
- `spec/effir.md` — how `Perform`/`op` are typed inside terms.
- `external/ocaml5-effects.md` — one-shot continuations, deep handlers, `Effect.Unhandled`, `match…with effect`.
- `spec/reference-semantics.md` — the pure Rocq handler for KV used in proofs/tests.
</content>
