---
id: effir
type: spec
summary: EffIR is a first-order, de-Bruijn, two-layer (pure val / effectful tm) typed term language; this file pins its v2 R12 grammar (ASCII case-fold prims, append-only Journal effect + floor-division prim, on top of bounded Fold, the expiring bytes-keyed store and Time), typing, and what is in and out of scope.
domain: spec
last-updated: 2026-07-13
depends-on: [adr-0001-first-order-ast, effect-signatures, adr-0008-general-match, adr-0009-vprim-registry, adr-0010-structured-values, adr-0011-time-and-expiring-store, adr-0012-list-elimination, adr-0013-journal-effect, adr-0014-wf-checker]
refines: []
related: [reference-semantics, codegen, error-taxonomy, runtime-manifest]
lint-max-lines: 210
---
# Spec — EffIR (the first-order effect IR)

> ⚠ **Slice-1 status:** the built subset differs — `VZero`/`VSucc` instead of `VPrim (list val)`,
> no `typecheck_ir.ml`.
> R2/R3 (2026-07-10): general `Match` replaces `MatchOpt` ([[adr-0008-general-match]]); `Prim`
> term + closed v1 prim set ([[adr-0009-vprim-registry]]).
> R7 (2026-07-11): `DTag`/`VTag`, `DList`/`VList`, `PTag` ([[adr-0010-structured-values]]).
> R4+R5 (2026-07-11): expiring **bytes-keyed store** (live iff `now_ms <= d`) + `Time`/`ONow`
> ([[adr-0011-time-and-expiring-store]]).
> R6 (2026-07-12): `Fold` term (the ONE list elimination) + prims
> `PMulChecked`/`PListLen`/`PListNth` ([[adr-0012-list-elimination]]; `theories/Fold.v`).
> R8 (2026-07-12): CONFIRMED CLOSED — error values carry **arbitrary dvals** incl. exact byte
> messages and `DTag` payloads; true since R1/M1, made deliberate in `theories/Fold.v` §R8.
> R9 (2026-07-12): **Journal** effect — `world.journal` + `OJournal` (append-only, write-only;
> frame law + run-sequence fold lemma proven GENERALLY in `theories/Journal.v`) and the
> `PDivFloor` prim ([[adr-0013-journal-effect]]).
> R10 v1 (2026-07-12): PROVEN **well-formedness** checker `wf_tm` (de Bruijn scope through
> Bind +1 / branch binders / Fold +2, exact op/prim arities; well-FORMED, never well-typed).
> Soundness GENERAL in `theories/Wf.v` (`wf_no_scope_stuck`: no out-of-scope `VVar` branch,
> ever; shape errors stay dynamic). Codegen wf-gates every program pre-emission with the
> EXTRACTED checker, no opt-out; emission core = `rocqeteer.codegen` ([[adr-0014-wf-checker]]).
> R12 (2026-07-13): prims `PLowerBytes`/`PUpperBytes` — ASCII case folding (adr-0009 discipline:
> ADR-free, manifest + diff-test; driver: case-insensitive option tokens; `theories/Prims.v` §6).

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
`prim` names resolve through the runtime manifest ([[runtime-manifest]]); an unregistered prim is a
codegen error ([[error-taxonomy]]). New prims are ADR-free but manifest + diff-test mandatory (adr-0009).

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
PMulChecked   DInt a, DInt b  -> DSome (DInt (a*b)) if in range, else DNone (R6; NB -1 * int64_min = 2⁶³ -> DNone)
PListLen      DList vs        -> DInt (length vs); shape mismatch -> DNone  (R6)
PListNth      DList vs, DInt i -> DSome v_i if 0 <= i < len; DNone otherwise (R6; bound checked in Z)
PDivFloor     DInt a, DInt b  -> DNone if b = 0 or result exits int64 (only int64_min / -1), else DSome
              (DInt (a/b)) — FLOOR (Rocq Z.div; realizer Z.fdiv, zarith Z.div truncates; driver: TTL rounding)
PLowerBytes   DBytes bs       -> DBytes: bytes 65-90 shifted +32; EVERY other byte unchanged incl. >127 (R12)
PUpperBytes   DBytes bs       -> DBytes: bytes 97-122 shifted -32; same non-letter posture — pure ASCII fold (R12)
```
**Strict parse grammar (DP1-DP8):**
DP1 empty input → DNone · DP2 leading '-' → negative, advance · DP3 digits empty after
sign (bare '-') → DNone · DP4 leading '0' → must be exactly "0"; more chars → DNone ("-0"
too) · DP5 leading non-digit ('+', space, other) → DNone · DP6 parse remaining digits,
non-digit in body → DNone · DP7 apply sign · DP8 range check [−2⁶³, 2⁶³−1] → DNone outside

Round-trip law: `apply_prim PPrintInt [DInt z] = DSome (DBytes bs)` implies
`apply_prim PParseInt64 [DBytes bs] = DSome (DInt z)` — proven for ALL in-range z
(`parse_print_roundtrip`, `theories/Prims.v`); 0/±1/int64_min/max also have vm_compute instances.

## Effectful computations (`tm`)
```
tm ::= Ret val                       (* pure result *)
     | Bind tm tm                     (* x <- t1 ;; t2 ; t2's context has one extra binder (de Bruijn 0 = x) *)
     | Perform op (list val)          (* trigger an effect operation with value arguments *)
     | Match val (list (pat * tm)) tm (* depth-1 general match: scrutinee, ordered branches, mandatory default *)
     | Repeat nat tm                  (* bounded loop: run body n times *)
     | Prim prim (list val)           (* pure primitive step: evaluate args, apply prim, yield dval; world unchanged *)
     | Fold val tm tm                 (* IR v2 R6: accumulator fold bounded by the list — Fold lst init body *)
```
`Prim p args` is a pure step — it evaluates each arg as a val, applies `apply_prim p`, and yields the
result as a dval. Bind sequences the result. Codegen emits `let vN = Prims.prim_<name> ... in`.

`Fold lst init body` ([[adr-0012-list-elimination]]): evaluate `lst`; run `init` for the starting acc;
per `DList` element **left to right**, run `body` with `push_env [elem; acc]` (**acc = db 0, elem = db 1**);
`body`'s result is the next acc; the final acc is the result. `OErr` from `init` or any iteration
short-circuits; the world threads. Non-`DList` scrutinee = **empty fold** (`init`'s result; its effects
still run once); R10 rejects it statically. Totality is structural on the finite list (no fuel). Codegen:
native `List.fold_left (fun acc elem -> BODY)`, binders `[acc; elem]` = db 0/1. Proofs: `theories/Fold.v`.

`op` references an operation of a declared effect signature ([[effect-signatures]]); its argument
and return types are fixed by that declaration. `run_top` takes `ctx` and `now`.

### Ops and the world — v2 R4+R5 ([[adr-0011-time-and-expiring-store]]), R9 ([[adr-0013-journal-effect]])
The `world` record bundles ALL ambient effect state: `kv` (the expiring store: a map from
byte-string keys to `(dval * option Z)` — value + optional absolute deadline in ms),
`ctx` (read-only Env context), `now_ms : Z` (the run's single instant, IMMUTABLE within a
run — the harness advances the clock between runs), `trace` (newest-first log),
`cache` (bytes-keyed memo, kept out of `observe`), and `journal : list (Z * dval)` (R9:
append-only, newest-first, exposed CHRONOLOGICALLY by `observe_full` alongside the trace;
write-only — no op reads it: frame law + run-sequence fold lemma, `theories/Journal.v`).
**Liveness is the ONE rule**: `(v, Some d)` is live iff `now_ms <= d` (alive AT the deadline, dead at d+1ms; oracle-validated,
12,500 cases); `(v, None)` is always live; expired = absent for every op AND for `observe`
(which filters by `now_ms`). Store op table (keys are `VBytes`; malformed args → `Dstuck`):
```
OGet         [k]     -> DNone | DSome v                       (live bindings only)
OPut         [k; v]  -> DUnit    stores v and CLEARS any deadline
ODelete      [k]     -> DBool    true iff a LIVE binding was removed
OGetDeadline [k]     -> DNone (no live k) | DSome DNone (live, no deadline) | DSome (DSome (DInt d))
OSetDeadline [k; VNone | VSome (VInt d)] -> DBool  true iff a live binding was modified
ONow         []      -> DInt now_ms                            (Time; no clock advance in-IR)
OJournal     [v]     -> DUnit    appends (now_ms, eval v) to world.journal (R9; entries of one
                        run share the run's instant; entries are plain dvals — consumers
                        encode commands via DTag/DList, no entry grammar in-IR)
OThrow [e] · OAsk [] · OTrace [v] · OCacheGet [k] · OCachePut [k; v]   (unchanged)
```
TTL policy (rounding, negative-expire-deletes, reply codes) is consumer-side, NOT IR semantics;
journal durability/fsync/replay-equivalence are consumer-side too (the realizer streams to a
sink — trusted via [[runtime-manifest]], never proven). Proofs: `theories/TimeStore.v` (boundary +
`<`-mutant rejection), `theories/KV.v` (`incr_correct`), `theories/Journal.v` (order/frame/composition).

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

Binder convention for PPair: `match_pat PPair (DPair a b) = Some [a; b]`; `push_env` pushes left-to-right,
so db0 = b (last pushed), db1 = a. `PTag z` matches `DTag z' v` iff `Z.eqb z z'`, yielding `[v]` (1 binder).

No nesting of patterns; no PVar/PWild — Match need not be exhaustive: the default arm covers all
unmatched cases (and wildcards).

## Structured values (R7, adr-0010-structured-values)
`DTag`/`VTag` inject a Z-tagged sum (multi-payload constructors nest `DPair`; nullary payloads use
`DUnit`); `DList`/`VList` build a finite sequence of values. Both are domain-neutral — a consumer
represents its own ADT by choosing tag numbers and composing `DPair`/`DTag`/`DList`. `DList` is
constructible, observable, and (since R6) eliminated by `Fold` / `PListLen` / `PListNth` — no PNil/PCons
patterns in v1 ([[adr-0012-list-elimination]] §Decision 4). `Match` dispatches on `DTag` via `PTag`; a
mis-tagged or non-`DTag` scrutinee falls to the default arm (the R10 typechecker will flag it statically).

## Binding discipline
De Bruijn indices throughout. `Bind t1 t2` extends the context by one for `t2`; `Match` branches extend it
by the pattern's bound-variable count. A surface notation layer may present named variables (elaborated to
de Bruijn before anything runs). Well-scopedness (`VVar n` has `n < |context|`) is a typechecker invariant.

## Typing (sketch)
Judgements `Γ ⊢ v : ty` (pure) and `Γ ⊢ t ÷ ty ! E` (computation of result type `ty`, effects in signature
`E`). Highlights:
- `Bind`: `Γ ⊢ t1 ÷ a ! E` and `Γ,a ⊢ t2 ÷ b ! E` ⇒ `Γ ⊢ Bind t1 t2 ÷ b ! E`.
- `Perform op vs`: `op` declared in `E` with arg types `as` and return `r`, `Γ ⊢ vs : as` ⇒ result `r`.
- `Match`: scrutinee type drives the required, exhaustive branch set; all branches share result type/effects.
The IR typechecker (`codegen/typecheck_ir.ml`) enforces arities, return types, scope, and exhaustiveness
**before** emission; failure is a codegen error, never a silent cast.

## In scope (v1)
`Ret`/`Bind`/`Perform`/`Match`; the value forms above; registered pure prims; a single effect or an explicit
sum of effects ([[effect-signatures]]); top-level non-recursive definitions (slice 1). Recursion (structural
/ bounded-int / fuel) came after the KV slice went green — see [[adr-0006-vertical-slice]].

## Out of scope (v1) — codegen MUST fail loudly (report §7.5)
First-class functions/closures in `val`; higher-order effect operations; dependent matches that would need
casts; cofixpoints; multi-shot continuations; well-founded recursion without compiled fuel/measure; calls
to unregistered prims/effects. A failed codegen beats an unsound one.

## Agent notes
> The `val`/`tm` split is deliberate and load-bearing: it keeps the reference interpreter **structurally
> recursive and total** (no effects hide inside a "pure" position) and makes `Bind` the *only* place a
> continuation lives — as a sub-term, not a closure. Do not collapse `val` and `tm` into one `expr`.

## Related files
- `spec/effect-signatures.md` — op/effect-sum declarations; `spec/reference-semantics.md` — the
  interpreter over `tm`; `spec/codegen.md` — the syntactic lowering of each `val`/`tm` form to OCaml.
