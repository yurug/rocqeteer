---
id: ext-index
type: index
summary: Routing table for external-dependency behavior — Rocq extraction, OCaml 5 effects, QCheck, zarith — the four pillars of the v1 dependency budget.
domain: external
last-updated: 2026-06-20
depends-on: []
refines: []
related: [index, adr-0003-dependency-budget]
---
# External dependencies — routing table

v1 depends on **only** these. No `coq-itree`/`MetaRocq`/`ext-lib`/`equations`/`malfunction`
([[adr-0003-dependency-budget]]).

| File | Dependency | The constraint that shapes us |
|------|------------|-------------------------------|
| `rocq-extraction.md` | Rocq 9.1 extraction plugin | copies `Extract Constant` unchecked; may insert `Obj.magic`; no complexity magic ⇒ extract a simple ADT, use the manifest |
| `ocaml5-effects.md` | OCaml 5.4 effect handlers | one-shot continuations, no static safety, runtime `Unhandled` ⇒ ban multi-shot, wrap entrypoints |
| `qcheck.md` | QCheck 0.91 | seedable generators + shrinking ⇒ adversarial differential tests with a corpus |
| `zarith.md` | zarith 1.14 | exact `Z` ⇒ default numeric model; bounded int is opt-in with a checked bound |

## Agent notes
> Each file documents *actual runtime behavior*, per the methodology — not API listings. The recurring theme:
> these tools are trusted, not proven; their quirks (unchecked extraction strings, one-shot continuations,
> uniform-sampling blind spots, silent int overflow) are the exact seams the premortem warned about.

## Related files
- `../architecture/decisions/adr-0003-dependency-budget.md` — why the set is exactly these four.
</content>
