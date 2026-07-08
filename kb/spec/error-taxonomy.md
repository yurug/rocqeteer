---
id: error-taxonomy
type: spec
summary: Enumerates every error class — codegen-time rejections, runtime errors, and CI/TCB build-failure conditions — with when each fires and what the user sees.
domain: spec
last-updated: 2026-07-08
depends-on: [codegen, runtime-manifest]
refines: []
related: [conv-error-handling, ext-ocaml5-effects, runbook-build-validate]
---
# Spec — Error taxonomy

> ⚠ **Slice-1 status:** most codegen error codes are statically unreachable (the reduced ADT can't
> represent the bad cases); live errors are the two arity/scope `Codegen_error`s. `run_checked` returns
> typed `` `Unhandled_effect ``/`` `Unexpected_exception `` (2 arms). See [[slice1-status]].

## One-liner
Three error surfaces: the codegen rejects bad input loudly, the runtime maps typed failures to a checked
result, and CI fails the build on any silent trust expansion.

## Scope
The closed set of error classes. Behavior of the runtime `ErrorE` backend is detailed in [[conv-error-handling]].

## 1. Codegen-time errors (emit nothing, non-zero exit, actionable message)
| Code | When | Message shape |
|------|------|---------------|
| `E_UNSUPPORTED_CONSTRUCT` | EffIR form outside the v1 fragment (closure, cofix, multi-shot, uncompiled recursion) | `unsupported: <form> at <path>; v1 fragment excludes it (see kb/spec/effir.md)` |
| `E_UNREGISTERED_PRIM` | `VPrim`/`Perform` op not in the manifest | `unregistered realizer '<name>'; add a manifest entry (kb/spec/runtime-manifest.md)` |
| `E_IR_TYPE` | arity / return-type / scope (`VVar` out of range) failure | `IR type error: <detail> at <path>` |
| `E_NONEXHAUSTIVE_MATCH` | branch set not exhaustive/redundant for scrutinee `ty` | `match on <ty> must cover {<ctors>}` |
| `E_CAST_REQUIRED` | lowering would need a cast not backed by an approved GADT witness | `refusing implicit cast at <path>; needs a reviewed witness` |
A failed codegen always beats a clever unsound one (report §7.5).

## 2. Runtime errors (typed, surfaced as `result`)
- `ErrorE`/`Throw` → OCaml exception backend behind a **checked runner** `run_error : (unit -> 'a) -> ('a, e) result` ([[conv-error-handling]]).
- `Effect.Unhandled eff` at a public entrypoint → `Error (\`Unhandled_effect (describe eff))`. Public APIs never leak unhandled effects (report §6.5).
- Unexpected exception at a public boundary → `Error (\`Unexpected_exception exn)`.
- Native realizer precondition violation (e.g. out-of-bounds, when checked) → typed error, not UB.

## 3. CI / TCB build-failure conditions (report §11.4, §12.3)
Build fails on: unregistered primitive; new `Axiom` without a review label; `Obj.magic` outside the one
approved witness module; `Effect.perform` outside generated/runtime modules; `external` C declaration not
registered; manually-edited generated file (hash mismatch); public entrypoint missing a differential test;
`Admitted`/`admit` present. The `docs/tcb_report.md` diff is itself a gate.

## Agent notes
> The taxonomy is a *trust* device, not just UX: each codegen-time rejection and each CI condition exists to
> stop an unsound or untracked path from reaching production. Adding a new "just make it compile" escape
> hatch is the anti-pattern this file forbids.

## Related files
- `conventions/error-handling.md` — Result-vs-exception policy and the checked runner.
- `runbooks/build-and-validate.md` — where these checks run in the pipeline.
</content>
