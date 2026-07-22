---
id: index
type: index
summary: Top-level routing for the Rocqeteer knowledge base — what the project is, how to read the KB, and quick-load bundles by goal.
domain: meta
last-updated: 2026-07-19
depends-on: []
refines: []
related: [glossary, prd, arch-overview, idx-by-task]
---
# Rocqeteer — Knowledge Base

## What this is
Rocqeteer is a **domain-independent** trusted toolchain to write effectful programs in Rocq, **prove** them
correct against a reference semantics, and **run** them as fast idiomatic OCaml 5 — with every trust
expansion named in a TCB report. v1 **proves functional correctness and measures (does not prove) non-functional
properties.** The architecture's load-bearing invariant: **one first-order EffIR is shared by the reference
interpreter and the codegen**, so the program proved and the program run cannot silently diverge.

## How to use this KB
- **New here?** Read in this order: `GLOSSARY.md` → `domain/prd.md` → `architecture/overview.md` →
  `architecture/decisions/INDEX.md` → `spec/INDEX.md` → `properties/INDEX.md`.
- **Have a task?** Go straight to `indexes/by-task.md` — it routes you to the ordered file set per task.
- **Wondering why?** Each ADR cites the premortem failure it defends against (`reports/premortem-idea-20260620.md`).
- Files are atomic and self-sufficient; titles are claims; links are glossed. Read the few you need, not all of them.

## Quick-load bundles (goal → ordered files)
| Goal | Load |
|------|------|
| Grasp the project | `GLOSSARY` · `domain/prd` · `architecture/overview` |
| Implement the KV slice | `spec/effir` · `spec/effect-signatures` · `spec/reference-semantics` · `spec/codegen` · `conventions/code-style` |
| Prove a spec | `spec/reference-semantics` · `properties/functional` · `adr-0005-anti-vacuity` · `conventions/testing-strategy` |
| Build/debug codegen | `spec/codegen` · `adr-0002-extraction-bridge` · `external/rocq-extraction` · `spec/error-taxonomy` |
| Add a realizer / axiom | `spec/runtime-manifest` · `adr-0004-trust-model` · `external/zarith` or `external/ocaml5-effects` |
| Write tests | `conventions/testing-strategy` · `properties/edge-cases` · `external/qcheck` |
| Build & validate / CI | `runbooks/build-and-validate` · `properties/non-functional` |
| Audit / review | `runbooks/audit-checklist` · `properties/INDEX` |
| Understand a decision | `architecture/decisions/INDEX` → the ADR → `reports/premortem-idea-20260620` |

## Map of the KB
- `GLOSSARY.md` — controlled vocabulary.
- `domain/prd.md` — product requirements, scope, success criteria.
- `architecture/INDEX.md` — overview, `decisions/` (19 ADRs — 0019 PROPOSED, awaiting review), and `architecture/tower-rationale.md`
  (why towers matter though mode F is byte-identical — the assurance-dial / evidence / TCB-growth /
  credibility arguments): pipeline, TCB layers, and the decisions behind them.
- `spec/` (8 + index) — EffIR, effect signatures, reference semantics, **program-logic** (the R14 shallow wp layer), codegen, runtime manifest, error taxonomy, **slice1-status** (built-vs-spec divergences — read first).
- `properties/` (3 + index) — functional (proven, P1–P8), non-functional (measured, NF1–NF6), edge cases (T1–T10).
- `external/` (`external/INDEX.md`) — Rocq extraction, OCaml 5 effects, QCheck, zarith (the entire v1 dependency budget).
- `conventions/` (`conventions/INDEX.md`) — code style, error handling, testing & proof hygiene.
- `runbooks/` (`runbooks/INDEX.md`) — build/validate pipeline, quality-audit checklist.
- `indexes/by-task.md` — task-oriented routing.
- `plan.md` (KV slice, done) · `plan-towers.md` (**phase C**: effect towers + application diversity — the current roadmap).
- `reports/` — `premortem-idea-20260620.{md,html}`; future audit/quiz reports.
- `questions-round1.md` — Phase-1 ambiguity resolution (answered: defaults accepted, NF = measure).

## File count
54 content/index files. Working artifacts live alongside: `questions-round1.md` (Phase-1 Q&A) and
`reports/` (premortem `.md`/`.html`, KB quiz, audits).

## Agent notes
> If code and a `spec/`/`properties/` file disagree, that is a finding — fix one, in the same change, and
> update `last-updated`. Stable paths: rewrite a file in place, never move it (broken links silently corrupt
> retrieval). The one decision never to reverse without re-reading the premortem: one EffIR, two backends.
</content>
