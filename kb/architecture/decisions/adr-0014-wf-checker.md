---
id: adr-0014-wf-checker
type: decision
summary: R10 v1 is a PROVEN well-formedness checker, not a full type system — wf_tm checks de Bruijn scope, op/prim arities, pattern binder counts and Fold/Match shape; its soundness theorem eliminates the scope class of Dstuck; the codegen refuses non-wf programs loudly; full value-shape typing is deferred phase 2 with a named open design question.
domain: architecture
last-updated: 2026-07-11
depends-on: [effir, adr-0008-general-match, adr-0009-vprim-registry, adr-0011-time-and-expiring-store, adr-0012-list-elimination]
refines: []
related: [codegen, error-taxonomy]
---
# ADR-0014 — R10 v1: a proven well-formedness checker (scope + arity), typed discipline deferred

## Context
Engine-scale IR programs are machine-written and large; today a bad de Bruijn index evaluates to `Dstuck`
(a runtime `Stuck` exception in generated code), a wrong `Perform`/`Prim` arity silently yields `DNone`,
and a mis-shaped `Match`/`Fold` falls to defaults — all discovered at run time, if at all. Requirement
R10: "extrinsic IR typechecker + codegen arity/scope checks; fail-loud". Constraints: honest claims
(prove what the checker guarantees; anti-vacuity), and the fact that FULL value-shape typing needs a type
universe for consumer-defined tagged sums (adr-0010) — a design with consumer input, not an overnight
decision.

## Decision
1. **Split R10.** v1 (this ADR) = **well-formedness**: everything checkable without a value-type
   universe. Phase 2 (future ADR, explicitly OPEN) = value-shape typing over a to-be-designed type
   grammar for dvals incl. tagged sums; its open question — how consumer ADT shapes (tag -> payload
   type) are declared and checked — is parked in the KB, not answered here.
2. **`wf_tm : nat -> tm -> bool` in Rocq** (the `nat` is the binding depth), checking structurally:
   - every `VVar i` satisfies `i < depth` (through `Bind` (+1), `Match` branch binders (+0/+1/+2 per
     pattern), `Fold` body (+2)); recursively into `VSome/VPair/VTag/VList` payloads
   - `Perform op args`: the op's exact arity (OGet 1, OPut 2, ODelete 1, OGetDeadline 1, OSetDeadline 2,
     ONow 0, OThrow 1, OAsk 0, OTrace 1, OCacheGet 1, OCachePut 2)
   - `Prim p args`: the prim's exact arity (from the adr-0009/0012 registry)
   - `Match`: patterns are welcome as-is (depth-1 by construction); branch bodies checked at the
     right extended depth; default at the same depth
   - `Repeat`/`Fold`/`Bind` shapes as defined.
3. **The soundness theorem (the claim, exactly):** for `wf_tm (length env) t = true`, evaluation never
   takes the out-of-scope `VVar` branch — no scope-`Dstuck` in `eval_val` anywhere in the run of `t`
   (stated via an instrumented or fuel-free structural argument over `run`). SHAPE errors (e.g. `VSucc`
   of a non-int, prim arg shape, non-DList Fold scrutinees) remain dynamic and are NOT claimed — the
   theorem's docstring says so in one sentence. Anti-vacuity: a concrete ill-scoped program that `wf_tm`
   rejects AND whose run hits `Dstuck`; a mutant checker that skips the `Fold` (+2) extension accepts a
   program whose run demonstrably sticks.
4. **Codegen gate:** `rocqeteer-codegen` runs the EXTRACTED `wf_tm` on every program before emission and
   fails the whole run with `program <name>: ill-formed (<first offending construct>)` on false — no
   opt-out flag. The single-source `all_programs` list is thereby wf-checked in CI forever.
5. **Naming discipline:** everything says *well-formed / wf*, never "well-typed" — the docs must not
   imply more than the theorem (invariant 3's wording rule).

## Consequences
- (+) The whole `Stuck`-from-scope class dies at build time, proven; machine-generated engine programs
  get immediate loud feedback with a construct-level location.
- (+) v1 needs no new value grammar — ships tonight-scale; phase 2 gets a clean seam (`wf_tm` becomes
  the outer check of a future `ty_tm`).
- (−) `DNone`-from-shape silences remain until phase 2 — accepted, documented, and already the posture
  of adr-0009/0012.
- (−) One more thing every new op/prim must update (its arity row); the checker's exhaustive match makes
  forgetting it a compile error, which is the point.

## What this means for implementers
- Prove soundness by induction on `tm` with the depth invariant; the `eval_val` lemma
  (`wf_val depth v = true -> length env = depth -> eval_val env v <> scope-stuck`) does the real work —
  consider making the scope-stuck case syntactically distinguishable (e.g. a dedicated helper for the
  nth lookup) WITHOUT changing runtime behavior, so the statement is clean.
- The codegen check runs on the extracted checker — one implementation, two uses (proof subject + CI
  gate); do NOT reimplement wf in OCaml.
- Tests: a deliberately ill-scoped tm in the codegen test path asserting the loud failure message;
  diff suites unchanged (wf programs only).
- vm_compute + existentials: explicit witnesses (theories/Prims.v header note).
