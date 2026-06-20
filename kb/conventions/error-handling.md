---
id: conv-error-handling
type: procedure
summary: Errors come only from a typed ErrorE effect or local control; the exception backend hides behind a checked runner, public entrypoints convert Effect.Unhandled and stray exceptions to typed results, and no arbitrary exceptions appear in generated code.
domain: conventions
last-updated: 2026-06-20
depends-on: [error-taxonomy, ext-ocaml5-effects]
refines: []
related: [codegen, runtime-manifest]
---
# Convention — error handling

## One-liner
Every failure is typed. Exceptions are allowed only as the *backend* of a typed `ErrorE` effect or for
local control inside a region; they never escape a public boundary uncaught.

## The ErrorE effect & backend (report §6.7)
Rocq models errors as `Variant ErrorE (E:Type) : Type -> Type := Throw : E -> ErrorE E Empty_set.` The OCaml
backend:
```ocaml
exception Runtime_error of Error.t
let throw e = raise (Runtime_error e)
let run_error f = try Ok (f ()) with Runtime_error e -> Error e
```
`Throw` returns `Empty_set` — there is no continuation, matching an exception's non-resumption.

## Result vs exception
- **Public APIs:** return `('a, error) result` (explicit). 
- **Hot internal paths:** the exception backend is allowed for speed, but only behind `run_error` and only
  for the registered `ErrorE` effect — never an ad-hoc `raise`.

## Checked entrypoint wrapper (report §6.5 / [[error-taxonomy]] T8)
Every generated public entrypoint is wrapped:
```ocaml
let apply_checked env input =
  try Ok (run_transaction env input) with
  | Effect.Unhandled eff -> Error (`Unhandled_effect (Runtime_effect_name.describe eff))
  | Runtime_error e      -> Error (`Runtime_error e)
  | exn                  -> Error (`Unexpected_exception exn)
```
So an unhandled effect or stray exception becomes a typed value, never a crash leaking out of the API.

## Rules (CI-enforced)
- No `raise` in generated code except the `ErrorE` backend; no exceptions for ordinary control flow.
- `Z.to_int`/bounds conversions handle their `Overflow`/range errors as typed errors ([[ext-zarith]]).
- Handler nesting (e.g. `run_error @@ run_trace @@ run_kv @@ entry`) is declared in the entrypoint manifest,
  not invented by codegen.

## Agent notes
> The premortem's T8 (effect escaping a public API) and the "no arbitrary exceptions" rule are the same
> discipline: the boundary is the only place failures become observable, and there they are always typed.

## Related files
- `spec/error-taxonomy.md` — the full enumeration of error classes.
- `external/ocaml5-effects.md` — why `Effect.Unhandled` must be caught at the boundary.
</content>
