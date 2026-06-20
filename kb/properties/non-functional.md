---
id: prop-non-functional
type: constraint
summary: Non-functional criteria NF1–NF6 are MEASURED with CI gates, never proven in v1 — covering no-free-monad-in-hot-path, allocation, determinism, latency regression, build reproducibility, and TCB-size budgets.
domain: properties
last-updated: 2026-06-20
depends-on: [prd, adr-0004-trust-model]
refines: []
related: [prop-functional, conv-testing-strategy, runbook-build-validate]
---
# Non-functional criteria (MEASURED, not proven — Phase 1 / A1 = "measure")

These are **measured with CI gates**, not proven. Formal cost/resource/WCET/space proofs are an explicit
v1 non-goal ([[prd]], [[adr-0004-trust-model]]). Do not write "proven"/"certified" about any NF item.

### NF1 — No free-monad interpreter in the hot path
*Criterion:* the executed code path contains no `Bind`/`Prog` interpretation; effect ops are direct calls.
*Measure:* CI-grep on `generated/` (shared with P3) + a benchmark smoke test asserting no interpreter
allocation signature. *Gate:* presence of an interpreter in a hot path fails the build.

### NF2 — Allocation budget per hot entrypoint
*Criterion:* minor/major allocations within a per-entrypoint budget (closures from binds, tuples from state
threading, option boxing should be near-eliminated by direct-style codegen). *Measure:* allocation profile
(`Gc`/statmemprof or a counting harness). *Gate:* >budget on a stable benchmark is a warning; tracked.

### NF3 — Determinism
*Criterion:* generated programs and tests give identical results across runs/machines — no reliance on hash
randomization, map iteration order, clock, locale, or platform `int` width (report §12.4). *Measure:* repeat
runs + (where relevant) two-platform check. *Gate:* a determinism diff fails CI.

### NF4 — Latency regression
*Criterion:* fast-path latency within an agreed factor of a baseline. *Measure:* `bench/` smoke on every PR,
longer runs nightly. *Gate:* **>10% regression on a stable benchmark fails the PR** (report §13.5).

### NF5 — Build reproducibility
*Criterion:* codegen output is byte-identical for identical inputs (shared with P4); generated-file hashes
match their headers. *Measure:* re-run-equality + hash check in CI. *Gate:* mismatch fails the build.

### NF6 — TCB size budget (engineering control, not a guarantee)
*Criterion:* codegen core ≤3000 LOC; runtime core ≤2000 LOC; each primitive module ≤500 LOC unless
separately reviewed; `Obj.magic` uses 0 by default (≤1 reviewed witness module); unregistered `Extract
Constant` = 0; C stubs = 0 in MVP. *Measure:* `tcb_report.md` line counts + grep. *Gate:* over-budget
requires an explicit review label.

## Agent notes
> "Measured" means a number in CI and a gate — not a theorem. If someone asks for a *proof* of a bound,
> that is the deferred research stretch, and it changes the architecture; route it back to the user, do not
> silently attempt it.

## Related files
- `properties/functional.md` — NF1/NF5 overlap with proven/CI-gated P3/P4.
- `runbooks/build-and-validate.md` — where each measure runs.
</content>
