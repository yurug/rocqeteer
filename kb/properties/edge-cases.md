---
id: prop-edge-cases
type: constraint
summary: Boundary inputs T1–T10 the differential and fault-injection tests must cover — overflow neighborhoods, missing keys, empty/large state, hash collisions, unhandled effects, and serialization corner cases.
domain: properties
last-updated: 2026-06-20
depends-on: [prop-functional, conv-testing-strategy]
refines: []
related: [error-taxonomy, conv-error-handling]
---
# Edge cases (T-entries) — what adversarial tests must hit

These exist because the refinement property P5 is *tested, not proven* ([[prop-functional]]); the premortem's
#3 failure is a divergence in a corner the generators never sampled. Generators are **adversary-biased**
toward these; each discovered divergence becomes a permanent corpus entry.

| ID | Boundary | Expected behavior |
|----|----------|-------------------|
| T1 | Integer extremes / overflow neighborhood (when `int63` realizer is used) | reference (`Z`) and fast agree, or the bounded realizer's checked bound triggers a typed error — never silent wraparound (C4) |
| T2 | `Get` on a missing key | both return `None` |
| T3 | Empty state / empty input | both handle without exception; codec encodes/decodes the empty value |
| T4 | Large state / large input (10^5+ entries/bytes) | agreement holds; no quadratic blowup surprise (perf tracked, NF) |
| T5 | Duplicate / repeated `Put` to same key | last-write-wins matches the `put;put` law (P7) |
| T6 | Hash collisions in the OCaml `Hashtbl` realizer | observable map contents still match the finite-map model |
| T7 | Map iteration-order dependence | normalization removes order; a result that depends on order is a determinism bug (NF3) |
| T8 | Unhandled effect escaping a public entrypoint | converted to `Error \`Unhandled_effect` ([[error-taxonomy]]); never an uncaught `Effect.Unhandled` |
| T9 | Codec: truncated / overlong / malformed bytes on `decode` | typed `Error`, never a crash or partial read; `decode` total |
| T10 | Codec: nested/compound encodings (pair-of-list-of-…) | round-trip P8 holds at depth; no length-prefix off-by-one |

## Fault injection (report §12.1)
Inject: missing key, bad bytes, out-of-bounds index, I/O error, unhandled effect, exception in a callback,
cache-corruption simulation — and assert the typed-error or agreement behavior above.

## Agent notes
> T1, T6, T7 are the ones most likely to pass uniform random testing and fail in production — weight
> generators toward them explicitly. A green differential suite that never exercised T1/T6/T7 is a warning
> sign, not a success (it is literally the premortem #3 early-warning signal).
> **Slice 1 (what `tests/diff_kv.ml` actually asserts):** **T1 N/A** (no `int63` realizer; `Z` cannot
> overflow). **Asserted by logged coverage count > 0:** T2 (key absent), T4 (large state), T5 (duplicate
> puts). **Structural (guaranteed, not counted):** T7 — the observable is a *sorted* assoc list, so
> iteration order cannot affect the result. **T8** is checked by fault injection (unhandled effect + stray
> exception → typed error). **T6** (internal `Hashtbl` collisions) occurs naturally under the small key
> range but is **not separately counted** in slice 1. This is the authoritative asserted set; see
> [[slice1-status]].

## Related files
- `conventions/testing-strategy.md` — generator bias, seed replay, corpus mechanics.
- `properties/functional.md` — P5/P8 these inputs stress.
</content>
