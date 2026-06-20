---
id: ext-qcheck
type: external
summary: QCheck 0.91 (qcheck-core) provides seedable random generators, shrinking, and a test runner; we use it for the adversarial differential tests with explicit seeds and a failing-input corpus.
domain: external
last-updated: 2026-06-20
depends-on: []
refines: []
related: [conv-testing-strategy, prop-functional, prop-edge-cases]
---
# External — QCheck 0.91 (`qcheck-core`, `qcheck-ounit`)

## One-liner
QCheck generates structured random inputs, shrinks failures to a minimal counterexample, and runs as a test.
We drive it with **explicit, recorded seeds** so every divergence is reproducible and corpus-able.

## Actual behavior we rely on
- **Generators** `'a QCheck.Gen.t` over a `Random.State.t`: `int_range lo hi`, `oneof`, `list`/`small_list`,
  `pair`, `option`, `map`, `frequency` (for **biasing** toward boundaries — [[prop-edge-cases]]).
- **Arbitraries** `'a QCheck.arbitrary` bundle a generator + (optional) shrinker + printer; shrinking yields a
  minimal failing input, which we persist.
- **Seeding/reproducibility:** the runner accepts a seed (`QCheck_base_runner`, `-s <seed>` / `~rand` with a
  `Random.State.make [|seed|]`). We always **log the seed** and pin failing seeds in the corpus.
- **Test:** `QCheck.Test.make ~count ~name arb prop`; integrates with OUnit/alcotest via backends.

## How we use it
- **Differential property (P5):** `prop input = normalize (reference input) = normalize (fast input)`, with
  generators **biased** toward T1–T10 (int extremes, collisions, empty/large, malformed bytes) rather than
  uniform — see [[conv-testing-strategy]] and [[prop-edge-cases]].
- **Metamorphic (P8):** encode/decode round-trip, parse/print/parse stability.
- **Corpus:** every shrunk counterexample is written to `tests/corpus/` and replayed on every run (regression).
- The **same seed** must reproduce the **same input** on both reference and fast sides (input distribution is
  shared, not regenerated independently).

## Caveats
- QCheck randomness uses OCaml `Random`; keep generation **off the determinism-sensitive runtime path** (it is
  test-only) so NF3 is unaffected.
- Uniform sampling under-covers boundaries — this is precisely the premortem #3 trap; bias deliberately.

## Agent notes
> Generator quality is a first-class deliverable, not glue. A passing P5 suite that never produced a T1/T6/T7
> input is a *warning*, not a success. Record seeds; never rely on "it passed once."

## Related files
- `conventions/testing-strategy.md` — the full test-layer design QCheck plugs into.
- `properties/edge-cases.md` — the boundaries generators must be biased toward.
</content>
