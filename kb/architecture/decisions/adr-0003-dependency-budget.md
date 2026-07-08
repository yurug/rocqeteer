---
id: adr-0003-dependency-budget
type: decision
summary: v1 depends only on rocq-stdlib, qcheck, and zarith; ITree, MetaRocq, ext-lib, equations, and malfunction are excluded as MVP blockers.
domain: architecture
last-updated: 2026-07-08
depends-on: [arch-overview]
refines: []
related: [adr-0001-first-order-ast, ext-rocq-extraction, ext-qcheck, ext-zarith]
---
# ADR-0003 — Minimal dependency budget for v1

## Context
The report leans on Interaction Trees (ITree) as its "canonical semantic model" and on MetaRocq/Malfunction
for the verified path and Mode B. On the actual toolchain (Rocq **9.1.1**), `opam install coq-itree` and
`coq-metarocq` return *"No package found"* (verified 2026-06-20). The post-rename Rocq 9.x ecosystem lags;
ITree's chain (paco, coq-ext-lib) targeted Coq ≤8.20. Building on absent/unported libraries is the
premortem's #2 failure (weeks lost to broken builds, or a forced semantic-core rewrite mid-project).

## Decision
v1 depends **only** on: **`rocq-stdlib` (9.0.0), `qcheck` (0.91), `zarith` (1.14)** — all installed and
working. **Excluded from v1:** `coq-itree`, `MetaRocq`/`MetaCoq`, `coq-ext-lib`, `coq-equations`,
`coq-malfunction`. The finite first-order EffIR ([[effir]]) needs none of them. An ITree bridge (for
coinductive reasoning) and MetaRocq-based Mode B become **optional later modules**, never MVP blockers.

## Consequences
- (+) The whole MVP builds on a verified-present toolchain; no opam archaeology.
- (+) Forces the simpler, more auditable finite-`tm` design instead of coinductive ITree codegen.
- (−) No coinductive/nontermination reasoning in v1; no automatic monadic-Gallina recognition (Mode B).
- (−) We re-implement small bits the ecosystem would otherwise provide (e.g. finite maps via stdlib).

## What this means for implementers
- **Day-one gate:** a dune+opam smoke build proving this dependency set compiles and that OCaml 5.4.1
  effects syntax (`match … with effect E, k -> …`, `Effect.Deep`) works. Block all other work behind it.
- Do not `Require Import` anything outside `rocq-stdlib`. New deps require a new ADR and a TCB-report entry.
- Prefer stdlib finite maps / lists; keep arithmetic on `zarith`'s `Z` by default ([[adr-0004-trust-model]] and C4).

## Related files
- `external/rocq-extraction.md`, `external/qcheck.md`, `external/zarith.md` — the three pillars' actual behavior.
- `architecture/decisions/adr-0001-first-order-ast.md` — why the finite design needs nothing exotic.
</content>
