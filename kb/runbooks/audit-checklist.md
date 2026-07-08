---
id: runbook-audit-checklist
type: procedure
summary: The multi-axis quality audit run after implementation — test gaps, security, performance, spec compliance, simplicity, provability, anti-vacuity, and TCB diff — each with what to check and where findings go.
domain: runbooks
last-updated: 2026-07-08
depends-on: [prop-functional, prop-non-functional, conv-testing-strategy, adr-0004-trust-model]
refines: []
related: [runbook-build-validate, runtime-manifest]
---
# Runbook — quality audit checklist (Phase 5)

## One-liner
After the pipeline is green, run one independent pass per axis (fresh perspective each), write findings to
`kb/reports/`, and Ralph-loop fix→re-audit until zero criticals.

## Axes
1. **Test-gap** — every P/NF/T entry: is it tested? Each function ≥1 test? Differential coverage of T1–T10? Add missing tests for full coverage.
2. **Anti-vacuity** — every `verifies`/theorem: read the *statement*; is `pre` inhabited; does a known-bad impl break it? Any `pre := False`/`post := True`? ([[adr-0005-anti-vacuity]])
3. **Security** — input validation at boundaries; no data exposure; `decode` total on malformed bytes (T9); no unsafe array/bytes access without a proven/checked bound.
4. **Performance (measured)** — allocation profile vs NF2 budget; no free-monad interpreter on hot path (NF1); latency vs baseline (NF4). Never phrase as "proven".
5. **Spec compliance** — for each `kb/spec/*` contract, does the code match? Code↔spec disagreement is a finding (fix one).
6. **Simplicity** — could the same result be reached more directly? Any second program representation creeping in beside EffIR? (reject — premortem #1)
7. **Provability** — for each change, which `kb/properties/*` entry explains why it is correct? If none, that is a gap.
8. **TCB diff** — `docs/tcb_report.md`: new axioms labeled? `Obj.magic` count 0 (or 1 reviewed)? unregistered `Extract Constant` = 0? LOC budgets (NF6)? every realizer has owner + tests?

## Process
- One fresh subagent per axis (independent perspective). Findings → `kb/reports/audit-<axis>-<date>.md`.
- Fix all critical + high; remaining highs documented with rationale. Ralph-loop (≤7) until 0 criticals; if
  not converging, return to planning and split the slice.

## Agent notes
> Axis 2 (anti-vacuity) and axis 8 (TCB diff) are the audits a normal code review would miss and the
> premortem says are fatal — do not let them be skipped because "the build is green." Green is necessary,
> not sufficient.

## Related files
- `runbooks/build-and-validate.md` — the pipeline this audit follows.
- `conventions/testing-strategy.md` — the test/anti-vacuity machinery the audit checks.
</content>
