---
id: adr-0009-vprim-registry
type: decision
summary: EffIR v2 adds a closed first-order primitive set applied via a Prim term — all prims TOTAL (fallible ones return option-encoded dvals so Match handles failure), each with a Rocq reference definition as spec and a manifest-registered OCaml realizer that is differentially tested.
domain: architecture
last-updated: 2026-07-10
depends-on: [effir, adr-0008-general-match, adr-0004-trust-model]
refines: []
related: [adr-0007-ir-v2-sizing, runtime-manifest]
---
# ADR-0009 — VPrim: total primitives, option-encoded failure, registry-backed realizers

## Context
IR v2 consumers need computation the IR lacks: bounds-checked integer arithmetic (int64 semantics — e.g. a
counter that must ERROR past 2⁶³−1, never wrap), byte-string operations (length/concat/slice), and a
STRICT decimal parse/print pair (optional `-`, no leading zeros except "0" itself, no whitespace/`+`,
entire input consumed, fits int64). Requirement R3. Constraints: first-order closed set (no user-extensible
prims in v1), totality of `run` preserved, trust model ADR-0004 (realizers are named, manifest-registered,
differentially tested), zero `Obj.magic`.

## Decision
1. **Term form** — `Prim : prim -> list val -> tm` (a pure step: evaluates args, applies the prim, yields
   `Ret`-like a dval). Values stay constructors/vars only; `Bind` sequences prim results; codegen emits a
   plain `let`.
2. **All prims are TOTAL.** Fallible operations return **option-encoded dvals** (`DNone` / `DSome result`),
   so failure handling is ordinary R2 `Match` — no new error machinery, no partiality in `run`. Arity or
   argument-shape mismatch (wrong dval constructor) yields `DNone` as well (the R10 typechecker will later
   reject such programs statically; semantics stays total meanwhile).
3. **The closed v1 set** (`prim` inductive):
   ```
   PAddChecked | PSubChecked      Z addition/subtraction, DNone if the result exits [−2⁶³, 2⁶³−1]
   PCmpInt                        DInt −1 | 0 | 1
   PEqBytes                       DBool (byte equality)
   PBytesLen                      DInt (length)
   PBytesConcat                   DBytes
   PBytesSub                      offset/len slice; DNone if out of range
   PParseInt64                    STRICT decimal grammar above; DNone on any violation or overflow
   PPrintInt                      canonical decimal rendering of an in-range DInt; DNone out of range
   ```
   Round-trip law worth proving now (cheap, high-value): `parse (print z) = Some z` for in-range z.
4. **Reference vs realizer**: each prim has a Rocq definition (the spec, used by `run`) and an OCaml
   realizer in `runtime/prims.ml` over `Rval.t` (native `bytes`/`Z.t`, fast). Every realizer is an entry in
   `docs/runtime_manifest.toml` + the TCB report (`Runtime_Prims_refines`), and the differential suites are
   extended with prim-heavy programs biased to the boundaries (±2⁶³ neighborhood, "0"/"-0"/"0123"/" 5"/"+5"/
   empty/non-digit bytes, slice edges).
5. **Codegen**: `Prim p [a;b]` → `let vN = Prims.p_impl a b in ...` — one registered symbol per prim, no
   inline reimplementation in generated code (the realizer is the single audited implementation).

## Consequences
- (+) Failure composes with Match: `Match (parse s) [(PSome, use it)] error-branch` is the whole pattern a
  command engine needs; exact error *messages* stay in the consumer's programs, not in the IR.
- (+) int64 semantics with Z values: no wrapping exists anywhere; bounds are explicit checks — satisfies
  ADR-0004's "bounded realizer needs a proven/checked bound" rule by construction.
- (−) Option-encoding makes ill-typed prim applications silently `DNone` until R10 — accepted, documented.
- (−) The prim set will grow per consumer needs; each addition is ADR-free but manifest+diff-test mandatory
  (a new prim without a manifest entry fails check_tcb).

## What this means for implementers
- Anti-vacuity: prove the parse/print round-trip + a concrete program using PParseInt64 through Match (both
  branches reachable: inhabitance on the DSome path, a mutant realizer/programs the statements reject).
- The strict-parse Rocq definition is the authoritative grammar; the OCaml realizer must be written FROM it
  (not from memory of scanf) and the differential generator must include every grammar-violation class.
