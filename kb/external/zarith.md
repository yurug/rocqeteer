---
id: ext-zarith
type: external
summary: zarith 1.14 provides arbitrary-precision Z used as the default faithful value model on both the reference and fast sides; bounded int63 is an opt-in, separately-reviewed realizer with a checked or proven bound.
domain: external
last-updated: 2026-07-08
depends-on: []
refines: []
related: [adr-0004-trust-model, runtime-manifest, prop-edge-cases]
---
# External — zarith 1.14 (`Z`)

## One-liner
`Z` is exact arbitrary-precision arithmetic. It is the **default** realizer for numeric `value`s so the
reference and the fast runtime cannot diverge by silent overflow — the premortem's #3 boundary trap.

## Actual behavior we rely on
- `Z.t` arbitrary-precision integers; total `Z.add`/`sub`/`mul`/`succ`/`pred`/`compare`/`equal`; conversions
  `Z.of_int`/`Z.to_int` (the latter raises `Z.Overflow` if out of range — a *checked* boundary, not silent).
- Deterministic, platform-independent results (good for NF3 determinism).
- Maps cleanly to Rocq `Z` for the reference model (faithful, not an approximation).

## Policy (C4 / [[adr-0004-trust-model]])
- **Default:** model numeric `value` as Rocq `Z` in the reference and realize to `Z` in the fast runtime —
  exactness over speed first. `value_succ` ⇒ `Z.succ`, `value_zero` ⇒ `Z.zero` (manifest entries).
- **Opt-in fast path:** a bounded `int63`/`int64` realizer is allowed **only** with a *proven or
  dynamically-checked* bound and a **separate review** ([[runtime-manifest]] validity rule 5). It must agree
  with the `Z` reference on T1 (overflow neighborhood) or raise a typed error — never wrap silently.

## Caveats
- `Z.to_int` can raise `Z.Overflow`; conversions at the runtime boundary must handle it as a typed error,
  not let it escape ([[error-taxonomy]]).
- `Z` allocates; for hot numeric loops the bounded realizer may be needed later — but only under the policy
  above, with differential coverage of the boundary.

## Agent notes
> Reaching for `int63` "for speed" without a bound is exactly how the most-dangerous failure ships. Default
> to `Z`; make any bounded realizer earn its place with a checked/proven bound, a T1 differential test, and
> an owner.

## Related files
- `architecture/decisions/adr-0004-trust-model.md` — proven/tested/measured split and the overflow trap.
- `spec/runtime-manifest.md` — how `Z`/`int63` realizers are registered and contracted.
</content>
