# Rocqeteer — project instructions

Rocqeteer is a **domain-independent** trusted toolchain to use **Rocq** as a certified programming language:
write effectful programs in Rocq, prove them against reference semantics, and run them as fast idiomatic
**OCaml 5** — with a small, explicit, auditable TCB. It is **not** tied to Tezos/Octez or any application
domain; treat any such reference as illustrative only.

## Start here
- The knowledge base is the source of truth: **read `kb/INDEX.md` first**, then `kb/indexes/by-task.md` for
  your task. Decisions live in `kb/architecture/decisions/`; the premortem that justifies them is
  `kb/reports/premortem-idea-20260620.md`.
- We follow the spec-driven methodology in `agentic-dev-kit/` (premortem → KB → plan → Ralph-loop implement →
  audit). Current phase is tracked in `SESSION_STATE.md` — read it at session start.

## Non-negotiable invariants (each defends a premortem failure mode)
1. **One first-order EffIR, two backends.** The reference interpreter and the codegen consume the *same*
   EffIR value. Never introduce a second program representation (no HOAS `Prog` beside a separate IR).
2. **v1 dependency budget = `rocq-stdlib` + `qcheck` + `zarith` only.** No `coq-itree`/`MetaRocq`/`ext-lib`/
   `equations`/`malfunction`. New deps need an ADR + TCB-report entry.
3. **Prove functional, MEASURE non-functional.** Never write "proven"/"certified" about performance.
   Formal cost/resource-bound proofs are a deferred research stretch, not v1.
4. **Anti-vacuity always.** Every Hoare/correctness theorem ships an inhabitance lemma (`∃ s, pre s`) and a
   proof-mutation test (a wrong impl must break the proof). Review reads *statements*, not theorem names.
5. **Adversarial differential testing.** Generators bias toward boundaries (overflow, collisions, empty/large,
   malformed bytes); log seeds; persist every counterexample to `tests/corpus/`. No uniform-only sampling.
6. **Vertical slice first.** KV must be green end-to-end (prove → extract → codegen → differential test)
   before any breadth. Do not warm up on easy modules while the integration risk waits.
7. **Trust is explicit.** Every realizer/axiom is in the runtime manifest and the TCB report. Forbidden by
   default: arbitrary `Obj.magic`, unregistered `Extract Constant`, `Effect.perform` outside generated/runtime
   modules, multi-shot continuations, C stubs, hand-edited generated files, `Admitted`/`admit` in commits.

## Workflow
- Confirm approach in 3–4 bullets before non-trivial implementation; do not start coding until the plan is
  approved. Complete each methodology phase fully (incl. tests) before the next.
- `make smoke` (dependency + effects-syntax check) runs first every session before trusting downstream results.
- Checkpoint to `SESSION_STATE.md` after each logical unit; commit WIP before a session ends.

## Toolchain (verified 2026-06-20, host: pangoline)
Rocq 9.1.1 · OCaml 5.4.1 · dune 3.23.0 · qcheck 0.91 · zarith 1.14 · opam switch `default`.
</content>
