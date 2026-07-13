---
id: idx-by-task
type: index
summary: Task-oriented routing — given what you are about to do (implement / prove / build codegen / add a realizer / test / audit / debug), the ordered files to load and the key questions they answer.
domain: meta
last-updated: 2026-07-13
depends-on: []
refines: []
related: [index, spec-index, prop-index]
---
# By-task routing table

Pick your task; load the files in order; the "answers" column says what you'll learn.

### Implement an EffIR program / add an effect
1. `domain/prd.md` · `architecture/overview.md` — what & how it fits.
2. `spec/effir.md` · `spec/effect-signatures.md` — grammar, typing, declaring effects.
3. `conventions/code-style.md` — literate/TDD style.
> Answers: Is my construct in the v1 fragment? How do I type a `Perform`? How do effects compose (sums)?

### Prove something (Hoare spec, law, refinement)
1. `spec/reference-semantics.md` — interpreter, `verifies`, KV handler, laws.
2. `spec/program-logic.md` — the shallow wp layer: rule inventory, store assertions, wp tactics (for ∀-quantified program theorems).
3. `properties/functional.md` — which P-entry am I establishing.
4. `architecture/decisions/adr-0005-anti-vacuity.md` · `conventions/testing-strategy.md` — inhabitance + mutation companions.
> Answers: What exactly must the theorem assert? What inhabitance lemma + mutant must accompany it? Instance (vm_compute) or general (wp rules)?

### Build / debug the codegen
1. `spec/codegen.md` — lowering table, emitted files, headers, fail-loud.
2. `architecture/decisions/adr-0002-extraction-bridge.md` — how EffIR arrives (extracted ADT).
3. `external/rocq-extraction.md` — extraction quirks (`Obj.magic`, unchecked strings).
4. `spec/error-taxonomy.md` — what to reject and how.
> Answers: How does each EffIR form lower? Why no JSON? When must codegen fail?

### Add a runtime realizer / refinement axiom (expand the TCB)
1. `spec/runtime-manifest.md` — entry schema + validity rules.
2. `architecture/decisions/adr-0004-trust-model.md` — proven/tested/measured + claim wording.
3. `external/zarith.md` / `external/ocaml5-effects.md` — the dep's actual behavior.
> Answers: What contract/tests/owner does my realizer need? Is this a new axiom (label it)? `Z` or bounded int?

### Write tests
1. `conventions/testing-strategy.md` — the layers + adversarial/seed/corpus discipline.
2. `properties/edge-cases.md` — T1–T10 to bias toward.
3. `external/qcheck.md` — generator/shrink/seed mechanics.
> Answers: What's the differential oracle? How do I bias toward boundaries? Where do counterexamples go?

### Build & validate / set up CI
1. `runbooks/build-and-validate.md` — the pipeline + hard-fail gates + slice-1 DoD.
2. `properties/non-functional.md` — the measured gates (NF1–NF6).
> Answers: What command sequence? Which conditions fail the build?

### Audit / review
1. `runbooks/audit-checklist.md` — the 8 axes.
2. `properties/INDEX.md` — proven/tested/measured map.
> Answers: What does a normal review miss here (anti-vacuity, TCB diff)?

### Understand why a decision is the way it is
1. `architecture/decisions/INDEX.md` → the specific ADR.
2. `reports/premortem-idea-20260620.md` — the failure it defends against.

## Related files
- `../INDEX.md` — top-level summary + quick-load bundles.
- `../spec/INDEX.md`, `../properties/INDEX.md` — finer routing within those areas.
</content>
