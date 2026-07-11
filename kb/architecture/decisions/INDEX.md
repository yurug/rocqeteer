---
id: adr-index
type: index
summary: Routing table for the six architecture decision records, each tracing to a premortem failure mode it defends against.
domain: architecture
last-updated: 2026-07-08
depends-on: []
refines: []
related: [index, arch-overview]
---
# ADRs — routing table

| ADR | Decision | Defends against (premortem) |
|-----|----------|------------------------------|
| `adr-0001-first-order-ast.md` | One first-order EffIR shared by interpreter & codegen; no HOAS `Prog` | #1 representation gap (most likely) |
| `adr-0002-extraction-bridge.md` | Convey EffIR via Rocq extraction to an OCaml ADT; no JSON in the TCB | #1 representation gap; TCB bloat |
| `adr-0003-dependency-budget.md` | v1 deps = rocq-stdlib + qcheck + zarith only | #2 missing ecosystem deps |
| `adr-0004-trust-model.md` | Prove functional, measure non-functional, name every refinement axiom | #3 false assurance; #4 NF over-promise |
| `adr-0005-anti-vacuity.md` | Inhabitance lemma + proof-mutation test per spec | #6 vacuous proofs |
| `adr-0006-vertical-slice.md` | KV green end-to-end before any breadth | #5 scope exhaustion; #7 fragment-too-small |
| `adr-0007-ir-v2-sizing.md` | IR v2 costs live in the runtime value universe, not proofs; dispatch ~12ns, no inlining | (spike-measured, 2026-07-10) |
| `adr-0008-general-match.md` | Match replaces MatchOpt: depth-1 patterns, mandatory default, first-match-wins, chained codegen | R2 design (2026-07-10) |
| `adr-0009-vprim-registry.md` | Total prims (option-encoded failure via Match), Rocq reference = spec, manifest-registered realizers | R3 design (2026-07-10) |
| `adr-0010-structured-values.md` | DTag (Z-tagged sums, PTag pattern) + DList values (no elimination until R6) — first-order ADTs cross the IR boundary | R7 design (2026-07-11) |

## Agent notes
> Every ADR exists because a specific failure mode would otherwise have killed the project. Before reversing
> one, re-read its premortem entry in `kb/reports/premortem-idea-20260620.md`.

## Related files
- `../overview.md` — how the decisions compose into the pipeline.
- `../../reports/premortem-idea-20260620.md` — the failure modes referenced above.
</content>
