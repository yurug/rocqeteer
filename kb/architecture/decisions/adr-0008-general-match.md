---
id: adr-0008-general-match
type: decision
summary: EffIR v2 replaces MatchOpt with one general first-order Match — depth-1 patterns (literals with 0 binders, constructors with fixed binders, mandatory default arm, first-match-wins) — total without a typechecker, guard-checkable via nested fix, compiled to chained direct-style OCaml matches.
domain: architecture
last-updated: 2026-07-10
depends-on: [effir, adr-0001-first-order-ast]
refines: [adr-0001-first-order-ast]
related: [adr-0007-ir-v2-sizing, codegen]
---
# ADR-0008 — General Match: depth-1 patterns, mandatory default, first-match-wins

## Context
IR v2 consumers (first: a RESP2 command engine) need to dispatch on **byte-string literals** (command
names, flags) and destructure options/pairs — `MatchOpt` covers only the last. Requirement R2 (downstream
contract). Constraints: invariant 1 (one first-order IR, two backends), extraction with zero `Obj.magic`,
`run` stays total and guard-checkable, proofs stay cheap pre-R10 (no exhaustiveness checker yet).

## Decision
1. **One new term form replaces MatchOpt** (no legacy duplication):
   `Match : val -> list (pat * tm) -> tm -> tm` — scrutinee, ordered branches, **mandatory default arm**.
2. **Patterns are depth-1, first-order**:
   ```
   pat := PUnit | PBool b | PInt z | PBytes bs     (literals — 0 binders, matched by dval equality)
        | PNone | PSome (binds 1) | PPair (binds 2) (constructor patterns — payloads at de Bruijn 0[,1])
   ```
   No nesting (compile nested matches as nested `Match` terms), no PVar/PWild (the default arm plays both
   roles; the scrutinee is already nameable by the program).
3. **Semantics**: evaluate the scrutinee to `d`; try branches in order; the first `pat` whose shape/literal
   matches `d` runs its body with the bound payloads pushed on the environment; no match → run the default.
   `match_pat : pat -> dval -> option (list dval)` is a total helper; `run` gains a nested fix over the
   branch list (same guardedness pattern as Repeat's inner fix — bodies are structural components).
   Totality holds **without** any typing assumption: the default arm makes Match complete on every dval.
4. **Codegen — branch-by-branch chaining**: each branch compiles to a single direct-style OCaml match with
   the next branch as fallback:
   `(match s with Rval.Some x -> body | _ -> NEXT)` for constructor patterns,
   `if Rval.equal s (Rval.Bytes "...") then body else NEXT` for literals; the chain ends at the default.
   Deterministic, no interpreter, no Bind — the existing gates apply unchanged.
5. **Migration**: all `MatchOpt` uses (samples, proofs, codegen, demo) are rewritten to
   `Match v [(PNone, t1); (PSome, t2)] default` where the old MatchOpt had no default — use the none-branch
   as default and keep `[(PSome, t2)]`? NO — keep it explicit and semantics-identical:
   `Match v [(PNone, t_none); (PSome, t_some)] t_none` (the duplicated default is dead code by totality of
   the two patterns on option-shaped scrutinees, but keeps the term honest without a typechecker).

## Consequences
- (+) Command dispatch, flag parsing, and option/pair destructuring in one uniform form; R10's future
  typechecker can later flag dead defaults instead of the IR needing exhaustiveness now.
- (+) `tm` becomes a nested inductive (list in a constructor) — extraction handles it first-order; concrete
  program proofs stay vm_compute/cbn; the auto-generated induction principle weakens, which no current
  theorem uses.
- (−) Every `destruct`/`match` on `tm` and the `run` fixpoint change shape: expected breakage across
  KV/Error/Env/Trace/Cache/Recur/BytesVal concrete proofs is mechanical (re-run with the new term spelling).
- (−) Dead default arms in migrated MatchOpt code — accepted; R10 will police them.

## What this means for implementers
- `match_pat` lives beside `eval`/`run` in EffIR.v; prove nothing general about it yet — anti-vacuity comes
  from a **dispatch sample**: a program matching a bytes scrutinee against two literals + default, proven by
  vm_compute, with a swapped-branches mutant rejected (first-match-wins made observable).
- The samples/codegen migration is one commit with the freshness + TCB gates as the net.
