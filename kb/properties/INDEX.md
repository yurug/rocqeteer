---
id: prop-index
type: index
summary: Routing table for Rocqeteer's properties — proven functional invariants (P), measured non-functional criteria (NF), and adversarial edge cases (T).
domain: properties
last-updated: 2026-07-08
depends-on: []
refines: []
related: [index, prop-functional, prop-non-functional, prop-edge-cases]
---
# Properties — routing table

| File | IDs | Status | Load when… |
|------|-----|--------|------------|
| `functional.md` | P1–P8 | **proven** (P5 tested) | writing proofs, codegen gates, or the refinement check |
| `non-functional.md` | NF1–NF6 | **measured** | wiring benchmarks/CI gates; never claim these are proven |
| `edge-cases.md` | T1–T10 | tested | building differential/fault-injection generators |

## The one distinction that matters
**Proven** (Rocq): functional equivalence to the reference, monad/state laws, codec round-trip, non-vacuity.
**Tested** (not proven): the reference/fast refinement P5 — it is an axiom, validated by adversarial diff.
**Measured** (not proven): everything in `non-functional.md` — numbers + CI gates, never theorems.

## Property → where enforced
- P3/P4/NF1/NF5 → CI-grep + `dune build` + golden/hash checks.
- P1/P2/P6/P7/P8 → Rocq proofs (+ inhabitance + mutation for P6).
- P5 + T1–T10 → adversarial differential tests + corpus replay.
- NF2/NF3/NF4/NF6 → benchmarks, determinism checks, `docs/tcb_report.md` budgets.

## Related files
- `../INDEX.md` — top-level routing and quick-load bundles.
- `../architecture/decisions/adr-0004-trust-model.md` — why proven/tested/measured are split this way.
</content>
