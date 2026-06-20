---
id: arch-overview
type: concept
summary: Rocqeteer's pipeline (EffIR → reference interpreter + codegen → OCaml), module structure, dependency graph, and three-layer TCB model.
domain: architecture
last-updated: 2026-06-20
depends-on: [prd, glossary]
refines: []
related: [effir, reference-semantics, codegen, runtime-manifest, adr-0001-first-order-ast, adr-0002-extraction-bridge, adr-0004-trust-model]
---
# Architecture overview

## One-liner
One first-order **EffIR** is the hinge: Rocq interprets it (reference, for proofs) and the codegen lowers
it to OCaml (fast, for running). Because both consume the *same* representation, "the program proved" and
"the program run" cannot silently diverge.

## Scope
The static module structure, the data-flow pipeline, the dependency graph, and the TCB layering. Detailed
contracts live in the `spec/` files; the *why* behind each choice lives in `architecture/decisions/`.

## Pipeline (data flow)
```
Rocq source (EffIR terms + effect sigs + reference handlers + Hoare specs + proofs)
        |
        |  (a) Rocq evaluates EffIR          (b) Rocq EXTRACTS the EffIR datatype to an OCaml ADT
        v                                        v
Reference interpreter (pure, in Rocq/extracted)   rocq-eff-codegen (OCaml tool)
        |  proof target + test oracle               |  consumes the SAME extracted EffIR value
        |                                            v
        |                                    Direct-style OCaml 5 (.ml/.mli) + effect decls + deep handlers
        +---------------------+----------------------+
                              v
                       Differential tests (reference vs fast, adversarial inputs)  +  TCB report
```
No JSON/serialization layer sits in the trusted path: the EffIR datatype is extracted to OCaml and the
codegen pattern-matches on it directly. See [[adr-0002-extraction-bridge]].

## Module structure (repo layout, created lazily per phase — report §14 + kb/)
```
theories/            Rocq sources
  Effects/           EffIR, effect signatures, reference interpreter, laws, Hoare layer
  RuntimeSpec/       Rocq specs for native realizers (bytes, int, error, …)
  Examples/          KV (slice 1), Codec (pilot)
  Extraction/        Extract-EffIR-to-OCaml-ADT directives
codegen/             OCaml tool: eff_ir.ml (mirrors extracted ADT), typecheck_ir.ml, emit_ocaml.ml,
                     emit_effects.ml, emit_handlers.ml, emit_mli.ml, emit_manifest.ml, main.ml
runtime/             Trusted OCaml runtime modules (runtime_error, runtime_bytes, … ) + manifest
generated/           Codegen output (.ml/.mli) — COMMITTED, hash-headed, never hand-edited
tests/               unit/ differential/ fuzz/ corpus/
bench/  ci/  docs/    benchmarks, TCB/forbidden-API checks, schemas + design notes
kb/                  this knowledge base
```

## Dependency graph (build order)
`theories/Effects` → `theories/Examples` + `theories/Extraction` → (extraction emits `codegen/eff_ir_in.ml`
data) → `codegen` builds → run codegen → `generated/` → links against `runtime/` → `tests/`.
External deps only: `rocq-stdlib`, `qcheck`, `zarith`. See [[adr-0003-dependency-budget]] and [[ext-rocq-extraction]].

## The two semantic artifacts
1. **Reference semantics** — pure Rocq interpreter over EffIR `tm`. Proofs target it. [[reference-semantics]]
2. **Fast semantics** — generated OCaml 5 with native handlers/data. Production runs it. [[codegen]]
Bridge: an explicit **refinement axiom** per effect, listed in the TCB report, checked by differential
tests. Never hidden. [[adr-0004-trust-model]]

## TCB layers (report §11)
- **Proof TCB** (keep conservative): Rocq kernel; explicitly imported axioms; tactics/plugins; logical
  assumptions in specs. Anti-vacuity discipline guards against meaningless specs. [[adr-0005-anti-vacuity]]
- **Extraction/runtime TCB**: Rocq extraction; `rocq-eff-codegen`; OCaml compiler + runtime + effect
  handler semantics; `runtime/` modules; manifest correctness. Budget: codegen ≤3000 LOC, runtime core
  ≤2000 LOC, 0 `Obj.magic` by default (≤1 reviewed witness module), 0 unregistered `Extract Constant`.
- **System TCB**: OS, build system, package manager, hardware. Out of our control; documented, not proven.

## Error hierarchy (summary; full taxonomy in spec/)
- **Codegen-time errors** — unsupported EffIR construct, unregistered realizer, IR type mismatch → fail
  loudly, emit nothing. A failed codegen beats an unsound one. [[error-taxonomy]]
- **Runtime errors** — typed `ErrorE` → OCaml exception backend behind a checked runner; `Effect.Unhandled`
  converted at public entrypoints. [[conv-error-handling]]

## Agent notes
> The invariant that justifies trusting the whole thing: reference and fast are generated from the **same
> EffIR value**. Any design change that reintroduces two representations (e.g. a hand-maintained IR beside
> an HOAS one) reopens the most-likely failure from the premortem — reject it. See
> [[adr-0001-first-order-ast]].

## Related files
- `spec/INDEX.md` — precise contracts for EffIR, interpreter, codegen, manifest, errors.
- `architecture/decisions/` — the ADRs behind every choice above.
- `reports/premortem-idea-20260620.md` — failure modes the architecture defends against.
</content>
