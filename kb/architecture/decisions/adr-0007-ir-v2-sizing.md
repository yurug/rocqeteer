---
id: adr-0007-ir-v2-sizing
type: decision
summary: Spike-measured IR v2 sizing — adding value constructors is cheap (proofs ~1 line each) but the runtime value universe (Kv.value, observe, diff-test comparators) is the real cost; effect dispatch is ~12ns/op so no codegen inlining is needed.
domain: architecture
last-updated: 2026-07-10
depends-on: [arch-overview]
refines: []
related: [adr-0001-first-order-ast, adr-0004-trust-model]
---
# ADR-0007 — IR v2 sizing (from the VBytes spike, branch spike/vbytes)

## Context
verdis (the first consumer; its KB file external/rocqeteer.md — in the verdis repo — holds requirements R0–R10) needs bytes values,
general match, primitives, an expiring store, and a Time effect. Spike V (2026-07-10, commits c940d5d +
3bb8ebf on `spike/vbytes`) measured the real cost before planning.

## Findings
1. **Constructor additions are nearly free at the proof layer**: `VBytes`/`DBytes` broke exactly 2 theorems
   (`incr_correct`, `decode_encode`), each a one-token destruct-arity fix (difficulty 1/5). Extraction: zero
   breakage. Codegen: +9 lines (emit case with escaping).
2. **The deferred cost is the runtime value universe**: `Kv.value = Z.t` is monomorphic; `observe` and every
   differential comparator are hardwired to `(Z.t * Z.t) list`. Nothing breaks until a program stores bytes
   through an effect — then runtime + all test comparators must generalize at once. This, not proofs, is the
   IR v2 core: estimated **4–6 focused sessions, dominated by the value-universe generalization**.
3. **Effect dispatch is negligible**: direct Hashtbl 17.9 ns/op vs deep-handler-dispatched ~30.5 ns/op
   (~12 ns overhead, ratio ≈1.7×). Cheap even against a trivial op.

## Decision
- IR v2 leads with the **value-universe generalization** (runtime dval-like sum + observable/comparator
  retyping) as its first milestone, since it gates everything and the type system gives no early warning.
- **No handler-inlining requirement (verdis's provisional R11) for v1** — dispatch is not a cost center;
  revisit only if a hot-path primitive cheaper than ~10 ns appears.
- Proof-repair budget per new constructor is ~1 line; do not over-engineer proof automation for this.

## What this means for implementers
The spike branch shows the exact edit sites: EffIR.v (ctors + eval case), codegen.ml `emit_val`,
`coqconv.mli`. The milestone plan for IR v2 starts from the runtime layer, not the theories layer.
