---
id: conv-code-style
type: procedure
summary: Literate, test-driven, small-unit style for Rocq and OCaml — file headers, doc on every public definition, WHY comments on conditionals, DI, function/file size limits, deterministic formatting.
domain: conventions
last-updated: 2026-06-20
depends-on: []
refines: []
related: [conv-error-handling, conv-testing-strategy, codegen]
---
# Convention — code style (Rocq + OCaml)

## One-liner
Write code that reads like a textbook on itself: explain the WHY and the non-obvious WHAT, keep units small,
and make output deterministic. Comments target ≥30% but never restate the code.

## Both languages
- **File header:** module purpose, spec references (`kb/spec/*` ids), key design decisions, links to relevant ADRs.
- **Literate + TDD:** start from a failing test that pins the property/gap (commit as a red baseline), then
  make it green. Test names start with the property id: `"P7: put then get returns Some v"`.
- **Small units:** functions < 30 lines, files < 200 lines; split when longer. KB files included.
- **No magic values:** every constant explained; every conditional carries a WHY comment.
- **Determinism:** any code-emitting or hashing path uses fixed ordering/formatting (NF5).

## OCaml (5.4.1)
- `.mli` for every module; keep effect constructors private behind signatures ([[effect-signatures]]).
- No `Obj.magic` outside the one approved witness module; no `Effect.perform` outside generated/runtime modules.
- DI everywhere (pass handlers/tables explicitly); no global mutable state. Errors via `result`/typed
  exceptions only ([[conv-error-handling]]); no stray exceptions.
- odoc-style doc comments on every public value/type: purpose, params (meaning), returns, raises, invariants (`@invariant P<N>`).

## Rocq (9.1.1)
- `Require Import` only from `rocq-stdlib` ([[adr-0003-dependency-budget]]).
- Every `Definition`/`Fixpoint`/`Variant`/`Record` gets a doc comment: intent, the spec id it realizes,
  totality/termination note.
- Every theorem: a one-line statement of *what it actually asserts* (so review checks meaning, not name),
  plus its anti-vacuity companions ([[adr-0005-anti-vacuity]]).
- No `Admitted`/`admit` in committed code; new `Axiom` only with a `tcb-axiom` review label and a manifest entry.

## Generated code
- Carries the "Do not edit manually" header with source path + manifest/contract hashes ([[codegen]]).
- Must still read as idiomatic OCaml — the point of direct-style codegen (G5).

## Agent notes
> The comment-ratio target is pedagogical, not bureaucratic: imagine writing the blog post that teaches this
> code. If a comment only restates the line, delete it; if the WHY is missing, that is the comment to write.

## Related files
- `conventions/error-handling.md` — the error policy referenced above.
- `conventions/testing-strategy.md` — the TDD/red-baseline loop in detail.
</content>
