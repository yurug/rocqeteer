---
id: conv-testing-strategy
type: procedure
summary: The test pyramid — unit, golden, adversarial differential (reference vs fast), metamorphic, fault-injection — plus the anti-vacuity proof gates (inhabitance + mutation) and seed/corpus discipline.
domain: conventions
last-updated: 2026-07-08
depends-on: [reference-semantics, prop-functional, prop-edge-cases, adr-0005-anti-vacuity]
refines: []
related: [ext-qcheck, runtime-manifest, runbook-build-validate]
---
# Convention — testing & proof-hygiene strategy

## One-liner
The reference interpreter is the oracle; the fast OCaml is tested against it on **adversarial** inputs; and
every proof must survive an inhabitance lemma and a mutation. Tests catch runtime divergence; anti-vacuity
gates catch meaningless proofs.

## Test layers (report §12.1)
1. **Unit** — each runtime module / realizer directly (its manifest contract).
2. **Golden** — fixed inputs, compare reference vs fast; plus a golden file of the `incr` *generated source*
   (proves P3 "no Bind/interpreter").
3. **Differential (the core, P5)** — `prop t s = normalize (reference t s) = normalize (fast t s)`. Inputs from
   **biased** QCheck generators ([[ext-qcheck]]) toward edge cases T1–T10 ([[prop-edge-cases]]). Normalization
   removes benign differences (map order, exception wrappers, trace timestamps).
4. **Metamorphic** — encode/decode round-trip (P8), parse/print/parse, cache/no-cache equivalence, commuting
   independent updates.
5. **Fault injection** — missing key, bad bytes, OOB index, I/O error, unhandled effect, callback exception.

## Adversarial generator policy (D3 — fights premortem #3)
- **Bias, don't sample uniformly:** weight toward integer extremes, overflow neighborhoods, hash collisions,
  empty/large/duplicate, malformed bytes.
- **Seed discipline:** every run logs its seed; the *same* seed yields the *same* input on reference and fast.
- **Corpus:** every shrunk counterexample is committed to `tests/corpus/` and replayed forever (regression).
- A green differential suite that never produced a T1/T6/T7 input is a **warning**, not a pass.

## Anti-vacuity gates (D1 / [[adr-0005-anti-vacuity]] — fights premortem #6)
For every `verifies`/correctness theorem:
- **Inhabitance:** prove `∃ s, pre sp s` (and that the postcondition is non-trivially reachable).
- **Mutation:** a deliberately-wrong implementation (or negated postcondition) for which the proof **fails**.
  Keep mutants in `tests/` (or in-file `Fail Theorem` checks). If a known-bad impl still satisfies the spec,
  the spec is vacuous → reject.
- Optionally, **proof mutation testing** at scale later (perturb proofs/specs; surviving mutants reveal weak specs).

## What proofs vs tests own (report §10.3)
- **Proofs:** functional correctness under the reference handler, invariants, round-trips (reference model),
  algebraic laws, bounds that justify any unsafe access, impossibility of dead cases.
- **Tests:** OCaml handler correspondence, native bytes/buffer behavior, Hashtbl/cache behavior, exception
  mapping, performance (measured), determinism.

## Agent notes
> Two distinct failure classes, two distinct defenses: *runtime* divergence → adversarial differential
> testing; *proof* vacuity → inhabitance + mutation. A project that does one but not the other still ships a
> premortem failure. Do both, early.

## Related files
- `external/qcheck.md` — the generator/seed/shrink mechanics.
- `runbooks/build-and-validate.md` — where each layer runs in CI.
- `properties/edge-cases.md` — the T-entries generators target.
</content>
