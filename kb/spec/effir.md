---
id: effir
type: spec
summary: EffIR is a first-order, de-Bruijn, two-layer (pure val / effectful tm) typed term language; this file pins its v2 R4+R5 grammar (expiring bytes-keyed store + Time), typing, and what is in and out of scope.
domain: spec
last-updated: 2026-07-11
depends-on: [adr-0001-first-order-ast, effect-signatures, adr-0008-general-match, adr-0009-vprim-registry, adr-0010-structured-values, adr-0011-time-and-expiring-store]
refines: []
related: [reference-semantics, codegen, error-taxonomy, runtime-manifest]
---
# Spec — EffIR (the first-order effect IR)

> ⚠ **Slice-1 status:** the built subset differs — `VZero`/`VSucc` instead of `VPrim (list val)`,
> no `typecheck_ir.ml`. IR v2 R2 (2026-07-10): general `Match` is implemented; `MatchOpt`
> is removed. See [[adr-0008-general-match]].
> IR v2 R3 (2026-07-10): `Prim` term + closed v1 prim set added. See [[adr-0009-vprim-registry]].
> IR v2 R7 (2026-07-11): `DTag`/`VTag` (tagged sum injection) and `DList`/`VList` (finite
> sequences) added to `dval`/`val`; `PTag` added to `pat`. No list elimination yet (R6).
> See [[adr-0010-structured-values]].
> IR v2 R4+R5 (2026-07-11): the Z-keyed KV is REPLACED by an expiring **bytes-keyed store**
> (per-binding optional deadline; live iff `now_ms <= d`), and `world` gains `now_ms` read
> by the new `Time` effect (`ONow`). See [[adr-0011-time-and-expiring-store]].

## One-liner
EffIR is the single first-order, explicit-binder representation that the reference interpreter evaluates
and the codegen lowers. Pure expressions (`val`) are separated from effectful computations (`tm`) so the
interpreter is total and the codegen is a direct syntactic translation.

## Scope
The v1 grammar, typing rules, binding discipline, and the in/out-of-scope construct list. The exact Rocq
constructor names are finalized during slice-1 implementation; this file fixes the **shape and invariants**
they must satisfy. Lowering to OCaml is in [[codegen]]; running in Rocq is in [[reference-semantics]].

## Types (`ty`)
```
ty ::= TUnit | TBool | TInt          (* TInt is zarith Z by default; see ADR-0004 / C4 *)
     | TOption ty | TPair ty ty
     | TNamed string                 (* abstract types realized via the manifest, e.g. "key","value","bytes" *)
```
Function types are **not** first-class values in v1: top-level definitions take a fixed arity of value
arguments and return a `tm`. No closures in EffIR values. (Keeps extraction simple — [[adr-0002-extraction-bridge]].)

## Pure expressions (`val`) — no effects, always terminating
```
val ::= VVar n                       (* de Bruijn index into the binder context *)
      | VUnit | VBool b
      | VInt z                       (* z : Z *)
      | VNone | VSome val
      | VPair val val
      | VBytes (list ascii)          (* binary byte string; evals to DBytes (IR v2 R1, 2026-07-10) *)
      | VPrim prim (list val)        (* call a registered PURE native realizer, e.g. value_succ, value_zero *)
      | VTag Z val                   (* tagged sum injection; evals to DTag z (eval_val env a) (IR v2 R7) *)
      | VList (list val)             (* finite sequence; evals to DList (map (eval_val env) vs) (IR v2 R7) *)
```
`prim` names resolve through the runtime manifest ([[runtime-manifest]]); an unregistered prim is a codegen
error ([[error-taxonomy]]).

## Closed v1 primitive set (`prim`) — IR v2 R3 (adr-0009-vprim-registry)
All prims are TOTAL. Fallible ones return **option-encoded dvals** (`DNone` / `DSome result`)
so failure is handled by ordinary `Match`. Arity/shape mismatch also yields `DNone`.
```
PAddChecked   DInt a, DInt b  -> DSome (DInt (a+b)) if in [−2⁶³, 2⁶³−1], else DNone
PSubChecked   DInt a, DInt b  -> DSome (DInt (a-b)) if in range, else DNone
PCmpInt       DInt a, DInt b  -> DInt (−1 | 0 | 1)
PEqBytes      DBytes a, DBytes b -> DBool (byte equality)
PBytesLen     DBytes bs       -> DInt (length)
PBytesConcat  DBytes a, DBytes b -> DBytes (a ++ b)
PBytesSub     DBytes bs, DInt offset, DInt len -> DSome (DBytes slice) or DNone if OOB
PParseInt64   DBytes bs       -> DSome (DInt z) under STRICT grammar (DP1-DP8), else DNone
PPrintInt     DInt z          -> DSome (DBytes decimal) if in-range, DNone if not
```
**Strict parse grammar (DP1-DP8):**
1. DP1: empty input → DNone
2. DP2: leading '-' → set negative flag, advance
3. DP3: digits empty after sign → DNone (bare '-')
4. DP4: leading '0' → must be exactly "0"; more chars after → DNone ("-0" also → DNone)
5. DP5: leading non-digit ('+', space, other) → DNone
6. DP6: parse all remaining digits; non-digit in body → DNone
7. DP7: apply sign
8. DP8: range check [−2⁶³, 2⁶³−1] → DNone if outside

Round-trip law: `apply_prim PPrintInt [DInt z] = DSome (DBytes bs)` implies
`apply_prim PParseInt64 [DBytes bs] = DSome (DInt z)` for all in-range z.
Proven for ALL in-range z (`parse_print_roundtrip` in `theories/Prims.v`); the critical
boundary values (0, ±1, int64_min/max) additionally have concrete vm_compute instances.

## Effectful computations (`tm`)
```
tm ::= Ret val                       (* pure result *)
     | Bind tm tm                     (* x <- t1 ;; t2 ; t2's context has one extra binder (de Bruijn 0 = x) *)
     | Perform op (list val)          (* trigger an effect operation with value arguments *)
     | Match val (list (pat * tm)) tm (* depth-1 general match: scrutinee, ordered branches, mandatory default *)
     | Repeat nat tm                  (* bounded loop: run body n times *)
     | Prim prim (list val)           (* pure primitive step: evaluate args, apply prim, yield dval; world unchanged *)
```
`Prim p args` is a pure step — it evaluates each arg as a val, applies `apply_prim p`, and yields the
result as a dval. Bind sequences the result. Codegen emits `let vN = Prims.prim_<name> ... in`.

`op` references an operation of a declared effect signature ([[effect-signatures]]); its argument and
return types are fixed by that declaration.

### Ops and the world — v2 R4+R5 ([[adr-0011-time-and-expiring-store]])
The `world` record bundles ALL ambient effect state: `kv` (the expiring store: a map from
byte-string keys to `(dval * option Z)` — value + optional absolute deadline in ms),
`ctx` (read-only Env context), `now_ms : Z` (the run's single instant, IMMUTABLE within a
run — the harness advances the clock between runs), `trace` (newest-first log), and
`cache` (bytes-keyed memo, kept out of `observe`). **Liveness is the ONE rule**: `(v, Some d)`
is live iff `now_ms <= d` (alive AT the deadline, dead at d+1ms; oracle-validated,
12,500 cases); `(v, None)` is always live; expired = absent for every op AND for `observe`
(which filters by `now_ms`). Store op table (keys are `VBytes`; malformed args → `Dstuck`):
```
OGet         [k]     -> DNone | DSome v                       (live bindings only)
OPut         [k; v]  -> DUnit    stores v and CLEARS any deadline
ODelete      [k]     -> DBool    true iff a LIVE binding was removed
OGetDeadline [k]     -> DNone (no live k) | DSome DNone (live, no deadline)
                        | DSome (DSome (DInt d))
OSetDeadline [k; VNone | VSome (VInt d)] -> DBool  true iff a live binding was modified
ONow         []      -> DInt now_ms                            (Time; no clock advance in-IR)
OThrow [e] · OAsk [] · OTrace [v] · OCacheGet [k] · OCachePut [k; v]   (unchanged)
```
TTL policy (rounding, negative-expire-deletes, reply codes) is consumer-side, NOT IR
semantics. `run_top` takes `ctx` and `now`; proofs: `theories/TimeStore.v` (boundary +
`<`-mutant rejection), `theories/KV.v` (`incr_correct` over the store, any instant).

### Patterns (`pat`) — IR v2 R2 (adr-0008-general-match), R7 (adr-0010-structured-values)
```
pat ::= PUnit | PBool b | PInt z | PBytes bs   (* literals — 0 binders, matched by equality *)
      | PNone                                   (* 0 binders *)
      | PSome                                   (* 1 binder: de Bruijn 0 = payload *)
      | PPair                                   (* 2 binders: db0 = second component, db1 = first component *)
      | PTag z                                  (* IR v2 R7: 1 binder: literal tag, db0 = payload *)
```
Semantics: evaluate the scrutinee; try branches in order (**first-match-wins**); the first matching
branch runs its body with bound payloads pushed left-to-right (last payload = de Bruijn 0); the
**mandatory default arm** runs on no match, making Match total without a typechecker.

Binder convention for PPair: `match_pat PPair (DPair a b) = Some [a; b]`; `push_env` pushes `[a; b]`
left-to-right, so db0 = b (second, last pushed), db1 = a (first).

`PTag z` matches `DTag z' v` iff `Z.eqb z z'`, yielding `[v]` (one binder, same convention as `PSome`).

No nesting of patterns; no PVar/PWild (the default arm covers wildcards).
Match need not be exhaustive — the default arm handles all unmatched cases.

## Structured values (R7, adr-0010-structured-values)
`DTag`/`VTag` inject a Z-tagged sum (multi-payload constructors nest `DPair`; nullary payloads use
`DUnit`); `DList`/`VList` build a finite sequence of values. Both are domain-neutral — no protocol-
specific constructor lives in the IR; a consumer represents its own ADT by choosing tag numbers and
composing `DPair`/`DTag`/`DList`. `DList` is constructible and observable (equality in `observe`/every
diff comparator) but has **no IR-level elimination until R6** — a consumer traverses a decoded `DList`
in its own pure Gallina after the boundary, not inside EffIR. `Match` dispatches on `DTag` via `PTag`;
a mis-tagged or non-`DTag` scrutinee falls to the mandatory default arm (same posture as adr-0009's
option-encoding: the R10 typechecker will later flag this statically).

## Binding discipline
De Bruijn indices throughout. `Bind t1 t2` extends the context by one for `t2`. `Match` branches extend the
context by the pattern's bound-variable count. A surface notation layer may present named variables; it
elaborates to de Bruijn before anything else runs. Well-scopedness (every `VVar n` has `n < |context|`) is
a typechecker invariant.

## Typing (sketch)
Judgements `Γ ⊢ v : ty` (pure) and `Γ ⊢ t ÷ ty ! E` (computation of result type `ty`, effects in signature
`E`). Highlights:
- `Bind`: `Γ ⊢ t1 ÷ a ! E` and `Γ,a ⊢ t2 ÷ b ! E` ⇒ `Γ ⊢ Bind t1 t2 ÷ b ! E`.
- `Perform op vs`: `op` declared in `E` with arg types `as` and return `r`, `Γ ⊢ vs : as` ⇒ result `r`.
- `Match`: scrutinee type drives the required, exhaustive branch set; all branches share result type/effects.
The IR typechecker (`codegen/typecheck_ir.ml`) enforces arities, return types, scope, and exhaustiveness
**before** emission; failure is a codegen error, never a silent cast.

## In scope (v1)
`Ret`/`Bind`/`Perform`/`Match`; the value forms above; registered pure prims; a single effect or an
explicit sum of effects ([[effect-signatures]]); top-level non-recursive definitions (slice 1). Recursion
(structural / bounded-int / fuel) is added **after** the KV slice is green — see [[adr-0006-vertical-slice]].

## Out of scope (v1) — codegen MUST fail loudly (report §7.5)
First-class functions/closures in `val`; higher-order effect operations; dependent matches that would need
casts; cofixpoints; multi-shot continuations; well-founded recursion without compiled fuel/measure; calls
to unregistered prims/effects. A failed codegen beats an unsound one.

## Agent notes
> The `val`/`tm` split is deliberate and load-bearing: it keeps the reference interpreter **structurally
> recursive and total** (no effects hide inside a "pure" position) and makes `Bind` the *only* place a
> continuation lives — as a sub-term, not a closure. Do not collapse `val` and `tm` into one `expr`.

## Related files
- `spec/effect-signatures.md` — how `op`s and effect sums are declared and typed.
- `spec/reference-semantics.md` — the interpreter over `tm`.
- `spec/codegen.md` — the syntactic lowering of each `val`/`tm` form to OCaml.
</content>
