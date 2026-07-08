---
id: adr-0004-trust-model
type: decision
summary: Functional correctness is proven against a reference model under explicit named refinement axioms; non-functional properties are measured, not proven; the certified claim is always qualified.
domain: architecture
last-updated: 2026-07-08
depends-on: [arch-overview, prd]
refines: []
related: [reference-semantics, runtime-manifest, conv-testing-strategy, prop-non-functional, adr-0005-anti-vacuity]
---
# ADR-0004 — Trust model: prove functional, measure non-functional, name every axiom

> **Slice-1 realization:** the refinement "axiom" is a documented **manifest assumption**
> (`docs/runtime_manifest.toml` `Runtime_KV_refines`), not a Rocq `Axiom` — so the Rocq development stays
> axiom-free (`Print Assumptions incr_correct` = "Closed under the global context"). It is validated by the
> differential tests, not declared in the logic. See [[slice1-status]].

## Context
The correctness guarantee bridges a *proven* Rocq reference and a *trusted* OCaml runtime via a refinement
**axiom** checked only by differential tests. The premortem's *most-dangerous* failure (#3): a runtime
divergence the tests never sampled (overflow, hash collision, iteration order) ships under a "certified"
badge that suppresses scrutiny. Separately, the user's goal mentions "nonfunctionally correct," but Phase 1
resolved this to **measure** (A1), since the architecture can prove functional equivalence but only measure
performance.

## Decision
- **Proven:** functional equivalence of the generated program to the Rocq reference semantics, **under the
  refinement axioms explicitly listed in the TCB report**. Each effect family has one named axiom
  (e.g. `Runtime_KV_refines`).
- **Trusted-and-tested (not proven):** the OCaml compiler, runtime, effect-handler semantics, and every
  realizer in the manifest. Validated by **boundary-/adversary-biased differential tests** ([[conv-testing-strategy]]).
- **Measured (not proven):** latency, allocations, determinism — CI regression gates only. Formal cost/
  resource/space-bound proofs are an explicit **v1 non-goal**. [[prop-non-functional]]
- **Claim wording (mandatory):** *"Functional equivalence to a Rocq reference model is machine-checked,
  under the refinement axioms in the TCB manifest. The OCaml compiler, runtime, handlers, and realizers are
  trusted and differentially tested, not proven."* Nothing is called "certified" without this qualifier nearby.

## Consequences
- (+) The trust boundary is narrow, named, and auditable; `Print Assumptions` + the manifest make it visible.
- (+) Honest external messaging; no false-assurance badge.
- (−) A realizer whose contract is wrong can still cause divergence — hence the adversarial differential
  testing and per-realizer contracts/tests are load-bearing, not optional.

## What this means for implementers
- Every refinement axiom is registered in `runtime_manifest` and surfaced in `docs/tcb_report.md`; a new axiom
  fails CI without a review label. [[runtime-manifest]]
- Differential generators must hit integer extremes, overflow neighborhoods, collisions, empty/large inputs;
  uniform-random-only is disallowed for trusted entrypoints. Store every divergence as a corpus entry. (D3)
- Never write "proven"/"certified" about performance. Default numeric realizer is `Z` (zarith), not wrapping
  `int63` (C4) — a bounded `int63` realizer needs a *proven or checked* bound and a separate review.

## Related files
- `conventions/testing-strategy.md` — differential/property/metamorphic/fault-injection layers.
- `spec/runtime-manifest.md` — realizer contracts and the axiom registry.
- `architecture/decisions/adr-0005-anti-vacuity.md` — keeping the *proven* half from being vacuous.
</content>
