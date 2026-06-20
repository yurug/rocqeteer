---
id: codegen
type: spec
summary: rocq-eff-codegen lowers an extracted EffIR value to direct-style OCaml 5 by erasing the monad (Bind→let, Perform→effect call, Match→match), emitting effect declarations, deep handlers, and an .mli, with deterministic formatting and loud failure on unsupported constructs.
domain: spec
last-updated: 2026-06-20
depends-on: [effir, effect-signatures, adr-0002-extraction-bridge]
related: [reference-semantics, runtime-manifest, error-taxonomy, ext-ocaml5-effects]
refines: []
---
# Spec — Code generation (rocq-eff-codegen)

## One-liner
The codegen consumes the extracted EffIR ADT and prints idiomatic direct-style OCaml 5 by **erasing the
monadic structure**: no `Bind` constructors, no free-monad interpreter survive into the output.

## Scope
The lowering rules per EffIR form, the files emitted, generated-file headers, determinism requirements, and
the fail-loud policy. Input arrival is [[adr-0002-extraction-bridge]]; effect/handler shapes are
[[effect-signatures]] and [[ext-ocaml5-effects]].

## Lowering rules (the core table)
```
EffIR                         OCaml
-----                         -----
Ret v                         compile_val v
Bind t1 t2                    let x = compile_tm t1 in compile_tm t2   (x = de Bruijn 0 of t2)
Perform (E,Op) [a;b]          E_effect.op (compile_val a) (compile_val b)
Match v [branches]            match compile_val v with | ... -> ...
VVar n                        the bound name for de Bruijn n (alpha-named on emit)
VInt z | VBool b | VUnit      literal
VSome v | VNone | VPair a b   Some (..) | None | (.., ..)
VPrim p [args]                <manifest OCaml symbol for p> (compile_val args...)
```
Each top-level EffIR definition becomes one OCaml `let name a1 … an = compile_tm body`. The result is plain
direct-style OCaml — effect operations look like ordinary function calls; their interpretation is supplied
by the handler installed around the entrypoint.

## Emitted files (report §7.4)
```
generated/
  <prog>_generated.ml / .mli     direct-style functions + public signature
  <prog>_effects.ml / .mli       type _ Effect.t += ... and perform wrappers (per signature)
  <prog>_handlers.ml / .mli      deep handlers (may be hand-written in runtime/ instead for slice 1)
  runtime_manifest.json          realizers + refinement axioms used
  tcb_report.md                  versions, axioms, Obj.magic, Extract Constant, entrypoints
```
Every generated file carries a header: tool name, source `.v` path, **effect-manifest hash**, **runtime
contract hash**, and `Do not edit manually.` A manually-edited generated file fails CI (hash mismatch).

## Handlers & placement
Deep handlers (`Effect.Deep`, reinstall across `continue`) interpret first-order effects, resuming each
continuation **exactly once** ([[ext-ocaml5-effects]]). They are installed at **stable region boundaries**,
not around every function; the entrypoint manifest declares the required handlers and their nesting order
(the codegen does not guess). Public entrypoints are wrapped to convert `Effect.Unhandled` into a typed
error ([[conv-error-handling]]).

## Determinism
Output must be byte-stable for the same input: fixed name-generation scheme for de Bruijn → identifiers,
fixed field/branch ordering, fixed pretty-printer settings. Determinism makes `generated/` diffs reviewable
and the hashes meaningful.

## Fail loud (report §7.5 / [[error-taxonomy]])
Reject (emit nothing, actionable error) on: unsupported EffIR construct, unregistered prim/effect op, IR
type/arity/scope/exhaustiveness failure, anything requiring a cast not backed by an approved GADT witness,
cofix, multi-shot, uncompiled well-founded recursion. **A failed codegen beats a clever unsound one.**

## Agent notes
> The single observable success criterion for slice 1's codegen: the emitted `incr` is exactly the
> direct-style `match KV_effect.get k with None -> … | Some x -> KV_effect.put k …` — **no `Bind`, no
> interpreter**. A `grep` for free-monad constructors in `generated/` is a CI gate (report Appendix A).

## Related files
- `spec/runtime-manifest.md` — where prim/op OCaml symbols and refinement axioms are resolved.
- `external/ocaml5-effects.md` — handler/`continue`/`Unhandled` semantics the output relies on.
- `spec/reference-semantics.md` — the behavior the output must differentially match.
</content>
