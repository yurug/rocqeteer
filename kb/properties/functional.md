---
id: prop-functional
type: constraint
summary: The functional invariants P1–P8 Rocqeteer must establish — monad/effect laws, interpreter determinism, structure-erasure in codegen, reference/fast refinement, and the codec round-trip — each with violation example, why, and test/proof strategy.
domain: properties
last-updated: 2026-06-20
depends-on: [reference-semantics, codegen, effir]
refines: []
related: [prop-non-functional, prop-edge-cases, adr-0004-trust-model, adr-0005-anti-vacuity]
---
# Functional properties (PROVEN, except where noted as tested)

Each: statement · violation example · WHY · strategy. "Proof" = Rocq; "Diff" = differential test;
"CI-grep" = static check. Refinement (P5) is the one *tested* (not proven) property — by design ([[adr-0004-trust-model]]).

### P1 — Monad laws for EffIR `Bind`/`Ret`
`Bind (Ret v) t = t[v]`, `Bind t (Ret (VVar 0)) = t`, and associativity, up to the interpreter's extensional
equality. *Violation:* `run` of `Bind (Ret v) t` differs from `run` of `t[v]`. *WHY:* `Bind`/`Ret` must be a
lawful monad or the surface notation and rewrites are unsound. *Strategy:* Proof. Companion: inhabitance is
trivial; mutation = a wrong `Bind` that drops the binding must break the law.

### P2 — Reference interpreter is total and deterministic
`run h env t s` terminates and is a function (same inputs → same output). *Violation:* a non-structural
recursion or a nondeterministic handler. *WHY:* it is the proof target and the test oracle; nondeterminism
or partiality destroys both. *Strategy:* Proof (structural `Fixpoint`; handlers are pure functions).

### P3 — Codegen erases monadic structure
No `Bind` constructor / free-monad interpreter appears in `generated/`. *Violation:* emitted `incr` builds a
`Prog`/`Bind` value instead of `let … = get k in …`. *WHY:* the entire performance thesis and the "idiomatic
OCaml" goal (G3). *Strategy:* CI-grep on `generated/` + golden-file check of the `incr` output.

### P4 — Codegen is well-typed & deterministic
Generated OCaml type-checks under OCaml 5.4.1, and codegen output is byte-stable for identical EffIR.
*Violation:* a `Perform` lowered with the wrong result type; nondeterministic name generation. *WHY:* type
errors mean a broken bridge; nondeterminism makes `generated/` diffs and hashes meaningless. *Strategy:*
`dune build` of `generated/` in CI + a re-run-equality check.

### P5 — Reference/fast refinement (TESTED, not proven)
For all inputs, `normalize (fast t s) = normalize (reference t s)`. *Violation:* OCaml `Hashtbl`/arithmetic
diverges from the reference map/`Z` model at a boundary (overflow, collision). *WHY:* this is the executable
correctness claim; it is an **axiom** ([[adr-0004-trust-model]]) we cannot prove, only test. *Strategy:*
Diff with **adversarial** generators + corpus replay ([[conv-testing-strategy]]); never uniform-only.

### P6 — Hoare specs are non-vacuous
Every `verifies` theorem has an inhabited precondition and is broken by a known-bad implementation.
*Violation:* `pre := fun _ => False` or `post := fun _ _ _ => True` slips through. *WHY:* the premortem's #6
— vacuous proofs certify nothing yet read as the strongest assurance. *Strategy:* Proof of `∃ s, pre s` +
mutation test ([[adr-0005-anti-vacuity]]); reviewer reads statements.

### P7 — KV state laws hold for the reference handler
`put k v ;; get k = put k v ;; ret (Some v)`; `put k v1 ;; put k v2 = put k v2`; `get k ;; get k = get k`.
*Violation:* `handle_kv` that doesn't overwrite on `Put`. *WHY:* these are the algebraic spec of state;
proofs and rewrites depend on them. *Strategy:* Proof against `handle_kv`.

### P8 — Codec round-trip (pilot)
In the reference model, `decode (encode x) = Ok x` for every value of the encoding's type. *Violation:* a
length-prefix off-by-one. *WHY:* it is the pilot's whole point and a canonical serialization correctness
property. *Strategy:* Proof in the reference model; Diff + metamorphic (encode/decode, parse/print/parse) on
the fast bytes implementation ([[prop-edge-cases]]).

## Agent notes
> P5 is the load-bearing *tested* property; treat its generator quality as a first-class deliverable, not an
> afterthought. P3/P4/P6 are cheap CI gates that catch the most dangerous regressions — wire them early.

## Related files
- `properties/non-functional.md` — the measured (not proven) criteria.
- `properties/edge-cases.md` — the boundary inputs P5/P8 must be tested against.
- `conventions/testing-strategy.md` — how P5/P8 are exercised.
</content>
