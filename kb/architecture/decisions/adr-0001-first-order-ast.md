---
id: adr-0001-first-order-ast
type: decision
summary: EffIR is one first-order, explicit-binder AST shared by the reference interpreter and the codegen; HOAS Prog is rejected.
domain: architecture
last-updated: 2026-07-08
depends-on: [arch-overview]
refines: []
related: [effir, adr-0002-extraction-bridge, adr-0003-dependency-budget]
---
# ADR-0001 — One first-order AST, not HOAS `Prog`

## Context
The source report (§5.3) models programs as `Prog E A := Ret A | Op X (E X) (X -> Prog E A)`. The `Op`
continuation is a **Gallina function** (higher-order abstract syntax). Gallina cannot inspect its own
function values, so such a term **cannot be traversed/serialized** into the first-order IR the codegen
needs — not without MetaRocq, which is not packaged for Rocq 9.1 ([[adr-0003-dependency-budget]]). The
premortem's *most-likely* failure is the team forking into an HOAS `Prog` (for proofs) and a separate
hand-maintained first-order IR (for codegen), which silently drift apart.

## Decision
Use **one** representation: **EffIR**, a first-order term language with **explicit binders (de Bruijn
indices)** and a two-layer split — pure `val` and effectful `tm` (`Ret`/`Bind`/`Perform`/`Match`). The Rocq
reference interpreter evaluates EffIR; the codegen lowers the *same* EffIR. A named-variable surface
notation gives ergonomics on top. v1 is **Mode A** (deep first-order DSL); **Mode B** (recognized monadic
Gallina via MetaRocq) is explicitly deferred. See [[effir]].

## Consequences
- (+) "Program proved = program run" is **structural**, not a hope: there is no second representation to drift.
- (+) No MetaRocq, no reflection, no serialization-of-closures problem.
- (−) Less ergonomic source than native Gallina monadic syntax; mitigated by notation. Accepted for v1.
- (−) The fragment is deliberately restricted (see [[effir]] for what is in/out). Unsupported constructs are codegen errors, by design.

## What this means for implementers
- Author programs as EffIR terms (helped by notation), **never** as HOAS `Prog`.
- Any proposal that adds a second program representation alongside EffIR must be rejected at review — it
  reopens the premortem's #1 failure.
- De Bruijn indices internally; keep a small `notation`/elaboration layer for named variables if needed.

## Related files
- `spec/effir.md` — the concrete grammar, typing, and well-formedness.
- `architecture/decisions/adr-0002-extraction-bridge.md` — how EffIR crosses into the codegen.
</content>
