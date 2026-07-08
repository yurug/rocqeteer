---
id: adr-0005-anti-vacuity
type: decision
summary: Every Hoare spec ships an inhabitance lemma and a proof-mutation test so that a compiling proof cannot be a vacuously-true one.
domain: architecture
last-updated: 2026-07-08
depends-on: [adr-0004-trust-model]
refines: []
related: [reference-semantics, conv-testing-strategy, prop-functional, runbook-audit-checklist]
---
# ADR-0005 — Anti-vacuity proof discipline

## Context
The implementation is largely AI-driven, and an agent optimizing for "QED achieved" can hollow out a spec:
`pre := fun _ => False` (vacuously true), `post := fun _ _ _ => True` (asserts nothing), proving a law over
a trivial case, or leaving `Admitted`. This is the premortem's #6 failure — *the proof-world analog of
plausible-but-wrong code*. Crucially, **vacuity is invisible to `Print Assumptions`** (no axioms, no
`Admitted`, just a worthless statement). A wall of green `QED`s then gives the strongest possible false
confidence precisely because "it's proved in Rocq."

## Decision
Every Hoare spec (and every nontrivial correctness theorem) must be accompanied by:
1. **An inhabitance lemma** — `∃ s, pre s` (and where relevant, a witness that the postcondition is
   non-trivially reachable). A spec whose precondition is unsatisfiable does not count as proven.
2. **A proof-mutation test** — a deliberately-wrong implementation (or a negated postcondition) that the
   proof **must reject**. If the proof still goes through against a known-bad impl, the spec is vacuous.
Reviews check theorem **statements**, not names or the QED count. CI greps for `Admitted`/`admit`/new
`Axiom` (without a review label) and fails.

## Consequences
- (+) A green proof now carries evidence about the *statement*, not just the derivation.
- (+) Mutation tests double as living documentation of what each spec actually forbids.
- (−) More obligations per theorem (inhabitance + at least one mutant). Accepted — it is the core defense of the whole "certified" claim.

## What this means for implementers
- When you state `verifies p {| pre; post |}`, in the same commit prove `Lemma <name>_pre_inhabited : ∃ s, pre s`.
- Add at least one mutant in `tests/` (or an in-file `Fail` check) demonstrating the proof breaks under a wrong impl/postcondition.
- Reviewer checklist: read every `pre`/`post`; reject specs whose precondition you cannot satisfy or whose postcondition you cannot violate with a wrong program. See [[runbook-audit-checklist]].

## Related files
- `conventions/testing-strategy.md` — where mutation/inhabitance live alongside differential tests.
- `properties/functional.md` — the invariants these specs are supposed to capture.
</content>
