---
id: adr-0010-structured-values
type: decision
summary: EffIR v2 R7 adds two domain-neutral value forms — DTag (Z-tagged sum injection, matched by a new depth-1 PTag pattern) and DList (list values, constructible and observable but with NO IR-level elimination until R6) — enough for consumers to represent any first-order ADT (e.g. a wire-reply type) across the IR boundary.
domain: architecture
last-updated: 2026-07-11
depends-on: [effir, adr-0008-general-match, adr-0009-vprim-registry]
refines: []
related: [adr-0007-ir-v2-sizing, runtime-manifest]
---
# ADR-0010 — Structured values: tagged sums + list values (R7)

## Context
Downstream engines must hand STRUCTURED results (e.g. a five-constructor wire-reply ADT, arrays included)
from generated IR code to a proven pure encoder. Requirement R7. The IR's value universe (dval) has
products/options/bytes/ints but no sums and no sequences, so such an ADT cannot cross the boundary today.
Constraints: rocqeteer stays domain-independent (no DReply / no protocol names in the IR — the concrete
ADT, its dval injection, and the encoder live in the consumer's theories, per the Codec.v pilot pattern:
pure Gallina proven + extracted, not IR programs); one IR, two backends; depth-1 Match discipline
(adr-0008); extraction with zero Obj.magic.

## Decision
1. **Two new value forms, both domain-neutral:**
   ```
   dval += DTag  : Z -> dval -> dval      (constructor-tagged value: sum injection)
        |  DList : list dval -> dval      (finite sequence of values)
   val  += VTag  : Z -> val -> val
        |  VList : list val -> val
   ```
   Multi-payload constructors nest `DPair`; nullary payloads use `DUnit`. Tags are `Z` (already in the
   universe, cheap equality — measured in adr-0007/0009; consumers name them with Gallina definitions,
   e.g. `Definition tag_error := 1`).
2. **One new pattern:** `PTag : Z -> pat` — depth-1, literal tag, binds the single payload at de Bruijn 0.
   Semantics via `match_pat`: `PTag z` matches `DTag z' v` iff `Z.eqb z z'`, yielding `[v]`. Nested payload
   destructuring is a nested `Match` (adr-0008 discipline unchanged).
3. **NO list elimination in R7.** `DList` is constructible (`VList`), observable (equality in `observe`/
   diff comparators), and traversable by CONSUMER PURE GALLINA after the boundary — but the IR gets no
   list pattern and no fold until R6 (which owns bounded iteration). Scope cut keeps R7 a pure
   constructor-addition milestone (~free per spike V) and avoids designing elimination twice.
4. **Runtime/codegen:** `Rval.t += Tag of Z.t * t | List of t list` (same-commit rule, kb/spec header);
   `Rval.equal` extended structurally (length mismatch = false). Codegen: `VTag z v` →
   `Rval.Tag (Z.of_string "…", v)`; `VList vs` → `Rval.List [ … ]`; `PTag z` branch →
   `(match s with Rval.Tag (t, x) when Z.equal t (Z.of_string "…") -> body | _ -> NEXT)`.
5. **eval_val**: `VTag z v` → `DTag z (eval_val env v)`; `VList vs` → `DList (map (eval_val env) vs)`
   (nested-inductive recursion, same shape as Match's branch list in `run`). The existing convention for
   stuck subvalues (wrapped, not propagated) is kept.

## Consequences
- (+) Any first-order ADT is now IR-representable as tagged values; the consumer proves
  `of_dval (to_dval x) = Some x` for ITS type and composes with its proven encoder — rocqeteer never
  learns protocol names.
- (+) Delivers R6's *value* half early; R6 shrinks to elimination (list pattern or bounded fold) only.
- (−) Tag discipline is the consumer's job until R10: `Match` on a mis-tagged value just falls to the
  default arm (same posture as adr-0009's option-encoding). Accepted, documented.
- (−) `dval` gains a second nested-inductive constructor (list in a constructor): the auto-generated
  induction principle weakens further — no current theorem uses it (same note as adr-0008).

## What this means for implementers
- Anti-vacuity: a sample program that CONSTRUCTS a tagged value (payload computed by a prim, list included)
  and a second program that MATCHES on two different tags + default; theorems by vm_compute for each
  reachable branch, an inhabitance lemma, and a swapped-tags mutant that the statements reject.
- Differential suite biased to: tag collisions (same payload, different tag), deep nesting
  (DTag over DPair over DList), empty/large lists, lists with mixed element shapes, tag values at
  Z boundaries. Coverage asserted.
- `observe`/`Rval.equal`/every diff comparator must handle the new constructors the SAME commit
  (M1's single-comparator design makes this one function: `Rval.equal`).
- vm_compute + existential goals: give explicit witnesses (see theories/Prims.v header note — the
  eexists/split blowup is real).
