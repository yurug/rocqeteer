---
id: adr-0002-extraction-bridge
type: decision
summary: EffIR crosses from Rocq to the codegen via Rocq extraction to an OCaml ADT consumed in-process; no JSON/serialization layer in the trusted path for v1.
domain: architecture
last-updated: 2026-06-20
depends-on: [adr-0001-first-order-ast]
refines: []
related: [effir, codegen, ext-rocq-extraction, adr-0004-trust-model]
---
# ADR-0002 — Bridge EffIR by extraction to an OCaml ADT

## Context
The codegen (an OCaml program) needs the EffIR term to lower. The report's "Option 1" emits JSON from a
deep-embedding printer; "Option 3" rewrites Rocq's extracted OCaml. Both add a trusted, fragile component
(a printer + a parser, or coupling to Rocq's OCaml output shape). Since EffIR is already a first-order Rocq
**datatype** ([[adr-0001-first-order-ast]]), Rocq's own extraction can emit it as a plain OCaml ADT.

## Decision
Convey EffIR to the codegen by **extracting the EffIR datatype (and the example terms) to an OCaml ADT**,
which the codegen consumes **in-process** by pattern-matching. The codegen's `eff_ir.ml` mirrors the
extracted ADT exactly. **No JSON/S-expression serialization sits in the v1 TCB.** A textual export
(JSON/sexp + snapshot tests) may be added later as *tooling*, outside the trust path.

## Consequences
- (+) Removes a printer and a parser from the TCB; fewer places to diverge; the ADT is checked by OCaml's type checker.
- (+) The extracted reference interpreter and the codegen input come from the same extraction run.
- (−) Couples `codegen/eff_ir.ml` to the extracted ADT shape — a mismatch is a compile error (loud, good), but the two must be kept in sync. A CI check compares the extracted `.mli` against the hand-written mirror.
- (−) Relies on Rocq extraction behaving predictably for this datatype; documented in [[ext-rocq-extraction]].

## What this means for implementers
- Keep EffIR's Rocq datatype simple and extraction-friendly (no fancy dependent indices in the *serialized*
  shape; keep type indices as proof-side refinements, not runtime data — see [[effir]]).
- When EffIR's datatype changes, regenerate the extracted ADT and update `codegen/eff_ir.ml` in the same change.
- Treat the extracted `eff_ir_in.ml` as a generated artifact (hash-headed); the codegen reads it, never edits it.

## Related files
- `external/rocq-extraction.md` — extraction behavior, `Obj.magic`/GADT caveats, what is and isn't checked.
- `spec/codegen.md` — how the codegen consumes the ADT and lowers it.
</content>
