---
id: spec-index
type: index
summary: Routing table for Rocqeteer's specification files — the precise contracts for EffIR, effects, reference semantics, codegen, manifest, and errors.
domain: spec
last-updated: 2026-06-20
depends-on: []
refines: []
related: [index, arch-overview]
---
# Spec — routing table

The contracts that implementation must satisfy. Read top-to-bottom for a first pass; jump by task otherwise.

| File | What it pins down | Load when you are… |
|------|-------------------|--------------------|
| `effir.md` | The first-order `val`/`tm` grammar, typing, binding, in/out-of-scope constructs | defining or extending the IR; deciding if a construct is supported |
| `effect-signatures.md` | How effects are declared in Rocq, mirrored to OCaml `Effect.t`, and summed | adding an effect family or its OCaml handler |
| `reference-semantics.md` | The pure Rocq interpreter, KV handler, the `Spec`/`verifies` Hoare layer, laws, anti-vacuity companions | writing proofs or the test oracle |
| `codegen.md` | The EffIR→OCaml lowering table, emitted files, headers, determinism, fail-loud rules | building or debugging `rocq-eff-codegen` |
| `runtime-manifest.md` | The realizer + axiom registry schema and validity rules | adding a realizer or a refinement axiom (expanding the TCB) |
| `error-taxonomy.md` | Codegen-time, runtime, and CI/TCB error classes | handling failures or wiring CI gates |

## Reading order for the KV slice (slice 1)
`effir.md` → `effect-signatures.md` (KV) → `reference-semantics.md` (handle_kv, incr_spec) →
`codegen.md` (the `incr` lowering) → `runtime-manifest.md` (value_succ, Runtime_KV_refines) →
`error-taxonomy.md` (gates).

## Agent notes
> Every file here is a *contract*: if code and spec disagree, that is a finding (fix one, in the same change).
> The load-bearing invariant across all of them is "one EffIR, two backends" — see `architecture/overview.md`.

## Related files
- `../INDEX.md` — the top-level KB routing table and quick-load bundles.
- `../architecture/overview.md` — how these contracts compose into the pipeline.
</content>
