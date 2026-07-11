---
id: adr-0012-list-elimination
type: decision
summary: R6 completes R7's list values with elimination — a bounded accumulator Fold term (body sees acc at db0, element at db1; error short-circuits; non-DList scrutinee yields the init accumulator until R10 types it) plus two prims PListLen/PListNth for arity checks and indexed access; no PNil/PCons patterns in v1.
domain: architecture
last-updated: 2026-07-11
depends-on: [effir, adr-0008-general-match, adr-0009-vprim-registry, adr-0010-structured-values]
refines: [adr-0010-structured-values]
related: [codegen, runtime-manifest]
---
# ADR-0012 — List elimination: bounded Fold + list prims (R6)

## Context
R7 (adr-0010) made lists constructible and observable but deliberately deferred elimination. Consumers now
need to CONSUME runtime-length lists: fold over a variadic argument vector (multi-key delete/exists),
build variadic replies, and extract the i-th argument with an arity check. `Repeat n` cannot do this — its
bound is a static `nat`. Constraints: totality of `run` (bounds must come from the data, which is finite),
first-order IR, depth-1 pattern discipline, prim-registry rules (adr-0009: new prims are ADR-free but
manifest + differential tests are mandatory).

## Decision
1. **One new term form — accumulator fold, bounded by the list:**
   `Fold : val -> tm -> tm -> tm` — `Fold lst init body`:
   evaluate `lst`; run `init` to produce the starting accumulator; for each element of the `DList`
   IN ORDER (left to right), run `body` in the environment extended with **acc at de Bruijn 0 and the
   current element at de Bruijn 1** (via the existing `push_env [elem; acc]` convention); `body`'s result
   is the next accumulator; the final accumulator is the result. An `OErr` from `init` or any `body`
   iteration short-circuits the whole Fold (Bind discipline). World state threads through iterations —
   effectful bodies are the point.
2. **Non-DList scrutinee → the fold is EMPTY** (result = init's result). Total without a typechecker,
   same posture as adr-0009's option-encoding of shape mismatch; R10 will reject such programs
   statically. No Dstuck, no new error machinery.
3. **Two new prims** (closed-set additions per adr-0009 §Consequences; both TOTAL):
   ```
   PListLen   [DList vs]         -> DInt (length vs)          ; shape mismatch -> DNone
   PListNth   [DList vs; DInt i] -> DSome v_i  if 0 <= i < len; DNone otherwise or on mismatch
   ```
   These give consumers arity checks and indexed argument access without folding. Realizers over
   `Rval.List` in `runtime/prims.ml`, manifest rows + `diff_prims` extension mandatory.
4. **NO list patterns (PNil/PCons) in v1.** Fold + PListLen/PListNth cover the named use cases; a
   structural cons pattern without general recursion invites head-only hacks. Revisit only with a use
   case Fold cannot express.
5. **Codegen** — direct style, no interpreter:
   `Fold lst init body` →
   `(match LST with Rval.List _l -> List.fold_left (fun vACC vELEM -> BODY) INIT _l | _ -> INIT)`
   with the binder names entering the env as [acc; elem] to match de Bruijn 0/1; `run`'s reference
   semantics uses a nested fix over the element list (Repeat/Match guardedness technique).

## Consequences
- (+) Variadic command surfaces (fold argv, build DList replies with Fold + PBytesConcat/VList) become
  expressible; with R4/R5 this completes the IR needs for a strings+expiry engine except R8-R10.
- (+) Totality argument is structural: the list is a finite dval; no fuel, no static bound.
- (−) A second binder-introducing construct after Match: de Bruijn bookkeeping in codegen gets one more
  case (same `_sN`/`vN` fresh-name discipline; body env is [acc; elem] + outer).
- (−) Silent empty-fold on non-list scrutinees until R10 — accepted, documented, same as prim mismatch.

## What this means for implementers
- Anti-vacuity: a sample folding a mixed DList with an effectful body (e.g. OPut per element + an
  int accumulator via PAddChecked), proven for a concrete list by vm_compute; an ORDER-observability
  theorem (a list and its reverse give different observable traces/accumulators) with a fold-right
  mutant rejected; an error-short-circuit theorem (body throws on element k → store shows exactly
  k prior puts); inhabitance; PListNth boundary lemmas (i = -1, 0, len-1, len).
- diff suite `diff_fold`: empty/singleton/large (1000+) lists, mixed shapes, error mid-fold,
  accumulator overflow paths through PAddChecked, non-list scrutinee; PListLen/PListNth rows join
  diff_prims with index boundary bias. Coverage asserted.
- vm_compute + existentials: explicit witnesses (theories/Prims.v header note).
