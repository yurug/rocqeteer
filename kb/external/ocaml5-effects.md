---
id: ext-ocaml5-effects
type: external
summary: OCaml 5.4 effect handlers are efficient but dynamically checked — continuations are one-shot, unhandled effects raise at runtime, deep handlers reinstall across continue, and the match-with-effect sugar needs 5.3+; these constraints shape the source fragment and the checked entrypoint wrapper.
domain: external
last-updated: 2026-06-20
depends-on: []
refines: []
related: [effect-signatures, codegen, conv-error-handling, error-taxonomy]
---
# External — OCaml 5 effect handlers (OCaml 5.4.1)

## One-liner
Effects give us direct-style execution of effectful programs, but OCaml does **no static effect checking**.
The runtime constraints below are why v1 bans multi-shot, resumes each continuation exactly once, and wraps
every public entrypoint to catch unhandled effects.

## Actual behavior & constraints (report §3.4, R6)
- **Declaration:** an effect extends the extensible GADT: `type _ Effect.t += Get : key -> value option Effect.t`.
- **Perform/handle:** `Effect.perform (Get k)` suspends to the nearest handler. With **5.3+** the sugar
  `match f () with | x -> … | effect (Get k), k_cont -> …` is available (we have 5.4.1). `Effect.Deep`/`Shallow`
  APIs also exist; **deep handlers reinstall themselves across `continue`**, which is what first-order ops need.
- **One-shot continuations.** A captured continuation may be resumed **at most once**; a second `continue`
  raises `Continuation_already_resumed`. ⇒ v1 handlers must `continue` exactly once per operation; **multi-shot
  / backtracking via effects is banned** (compile nondeterminism to explicit lists instead).
- **No static safety.** An unhandled effect raises `Effect.Unhandled` **at runtime**. ⇒ every public
  entrypoint is generated/wrapped to convert `Effect.Unhandled` into a typed `Error` ([[error-taxonomy]] T8).
- **No leak guarantee.** OCaml does not ensure a captured continuation is ever resumed; dropping one can
  retain resources. ⇒ handlers resume on every branch; linter/review for scheduler-like handlers.
- **C boundary.** Effects cannot cross some C-to-OCaml callback boundaries. ⇒ no C stubs in MVP ([[prop-non-functional]] NF6).
- **Performance:** implemented with runtime-managed fibers; capturing/resuming does not copy stack frames, so
  suspension/resumption is cheap — but handlers are *not free* (avoid one-handler-per-tiny-call; place at
  region boundaries — [[codegen]] §handlers).

## What this means for our code
- Generated effect ops are thin `perform` wrappers; raw `Effect.perform` is **banned outside generated/runtime
  modules** (CI grep, [[error-taxonomy]]).
- The KV handler is a deep handler over a `Hashtbl`, `continue`-ing once per op ([[reference-semantics]] mirror).
- Handler nesting order is declared in the entrypoint manifest, not guessed by codegen.

## Agent notes
> The three premortem-relevant traps: (1) a handler that forgets to `continue` (hang/leak) or continues twice
> (raises); (2) an effect that escapes a public API (uncaught `Unhandled`); (3) reaching for effects to model
> backtracking. All three are forbidden-by-construction in v1 — keep them that way.

## Related files
- `spec/effect-signatures.md` — the Rocq↔OCaml `Effect.t` mirror.
- `conventions/error-handling.md` — the checked runner that catches `Unhandled`/exceptions at the boundary.
</content>
