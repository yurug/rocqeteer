---
id: conv-index
type: index
summary: Routing table for Rocqeteer coding/testing conventions — code style, error handling, and the testing+proof-hygiene strategy.
domain: conventions
last-updated: 2026-07-08
depends-on: []
refines: []
related: [index]
---
# Conventions — routing table

| File | Covers | Load when… |
|------|--------|------------|
| `code-style.md` | Literate/TDD style, headers, doc, size limits, determinism (Rocq + OCaml) | writing any code |
| `error-handling.md` | Typed errors, `ErrorE` backend, checked entrypoint wrapper, no stray exceptions | handling failures or wiring entrypoints |
| `testing-strategy.md` | Test pyramid, adversarial differential testing, anti-vacuity (inhabitance+mutation), seeds/corpus | writing tests or proofs |

## Agent notes
> `testing-strategy.md` is the most load-bearing: it operationalizes the two trust defenses (adversarial diff
> for runtime divergence, anti-vacuity for proof vacuity). Read it before writing the first test or proof.

## Related files
- `../INDEX.md` — top-level routing.
- `../architecture/decisions/adr-0004-trust-model.md` / `../architecture/decisions/adr-0005-anti-vacuity.md` — the decisions these enact.
</content>
