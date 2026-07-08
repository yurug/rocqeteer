---
id: adr-0006-vertical-slice
type: decision
summary: No breadth is added until one example (KV) is green end-to-end through the full pipeline; this defends against scope exhaustion.
domain: architecture
last-updated: 2026-07-08
depends-on: [prd]
refines: []
related: [adr-0001-first-order-ast, prop-functional, runbook-build-validate]
---
# ADR-0006 — Vertical slice first, breadth never before green

## Context
The report's six-phase roadmap and six parallel task groups invite breadth-first work. The premortem's #5
failure: ~5000 lines of half-finished modules, dozens of `Admitted`, and *zero* examples crossing the full
proof→fast-OCaml→differential-test path, until momentum dies. Agents are especially prone to this — lateral
moves to "cheaper" modules feel like progress.

## Decision
**One thin vertical slice, end-to-end, before any breadth.** Slice 1 is **KV** (`Get`/`Put`/`Delete` + an
`incr` program): write it as EffIR, prove `incr_spec` (with inhabitance lemma, [[adr-0005-anti-vacuity]]),
extract the reference interpreter, generate direct-style OCaml + a deep handler, and pass a boundary-biased
differential test — all green and committed. **Only then** is a second effect family, runtime module, or
codegen feature allowed to start. We track a counter "green end-to-end examples"; it must be ≥1 before breadth.

## Consequences
- (+) Forces the riskiest integration questions (EffIR ↔ extraction ↔ codegen ↔ handler) to be answered first, on the smallest possible example.
- (+) Always-shippable: there is a working demonstration of the core value at every step.
- (−) Feels slower early (no broad scaffolding); the slice may surface a hard problem that forces re-plan — which is exactly the point of doing it first.

## What this means for implementers
- Within slice 1, attack the riskiest sub-task first: getting the *same* EffIR value to drive both the
  extracted reference and the codegen ([[adr-0002-extraction-bridge]]). Prove a 3-node program survives
  Rocq→extract→codegen→run before fleshing out `incr`.
- Do not start Error/Env/Trace/Cache, GADT witnesses, or extra runtime modules until KV is green end-to-end.
- If slice 1 stalls past its Ralph-loop budget, stop and split it — do not pivot to easier modules.

## Related files
- `runbooks/build-and-validate.md` — the end-to-end build/extract/codegen/test sequence the slice must pass.
- `properties/functional.md` — the properties slice 1 must demonstrate (refinement, structure-erasure).
</content>
