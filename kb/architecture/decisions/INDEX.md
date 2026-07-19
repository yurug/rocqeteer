---
id: adr-index
type: index
summary: Routing table for the architecture decision records, each tracing to the premortem failure mode or design review it defends against.
domain: architecture
last-updated: 2026-07-19
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
| `adr-0011-time-and-expiring-store.md` | Time effect (ONow, per-run now_ms) + bytes-keyed store with deadlines replacing Z-keyed KV; live iff now <= d; one injected time source | R4+R5 design (2026-07-11) |
| `adr-0012-list-elimination.md` | Bounded accumulator Fold (acc db0, elem db1; error short-circuits) + PListLen/PListNth prims; no PNil/PCons | R6 design (2026-07-11) |
| `adr-0013-journal-effect.md` | Journal effect: OJournal appends (now_ms, dval); order + frame laws + generic run-sequence fold lemma; durability = named consumer trust | R9 design (2026-07-11) |
| `adr-0014-wf-checker.md` | R10 v1 = PROVEN wf checker (scope+arity; kills scope-Dstuck at build time; codegen refuses non-wf); value-shape typing = open phase 2 | R10 design (2026-07-11) |
| `adr-0015-program-logic.md` | R14 = shallow wp over run (no second semantics): rules per construct/op/prim, keyed store assertions, Repeat/Fold invariant rules, wp_* tactics — the road to forall-quantified specs and the consumer's crown-jewel replay theorem | R14 design (2026-07-13) |
| `adr-0016-effect-towers.md` | Effect towers: 7-op kernel / 5 derived ops (Expiry, Cache, Journal) discharged by proven elaborations + refinement theorems; mode-K (kernel-only) execution in CI; manifest `discharge` field | design review 2026-07-19 ("chosen-for-redoq" + TCB-descent critiques) |

## Agent notes
> Every ADR exists because a specific failure mode would otherwise have killed the project. Before reversing
> one, re-read its premortem entry in `kb/reports/premortem-idea-20260620.md`.

## Related files
- `../overview.md` — how the decisions compose into the pipeline.
- `../../reports/premortem-idea-20260620.md` — the failure modes referenced above.
</content>
