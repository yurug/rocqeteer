---
id: slice1-status
type: spec
summary: What slice 1 actually implements vs. the (aspirational) spec files — the authoritative record of divergences after Phase 4-5, so a reader is never misled by a spec describing unbuilt machinery.
domain: spec
last-updated: 2026-06-21
depends-on: [effir, codegen, runtime-manifest, error-taxonomy, adr-0004-trust-model]
refines: []
related: [plan, prop-functional]
---
# Slice-1 implementation status (built vs. spec)

## One-liner
The KV vertical slice is built, green (`make all`), and committed. Several `spec/` files describe a fuller
design than slice 1 implements; this file is the single source of truth for what exists, what diverges, and
why. When a `spec/` file and the code disagree, **this note governs for slice 1**.

## What is built (and verified)
- **EffIR** (`theories/EffIR.v`): extrinsic first-order `dval`/`val`/`op`/`tm` with a `Dstuck` sentinel; a
  **total** reference interpreter `run : … -> world -> outcome * world` (world = { kv; ctx; trace }) (`outcome = ORet | OErr`) over
  `FMapAVL(Z_as_OT)`, where `Bind` short-circuits on `OErr`; `incr_at`, `prog0`, and `theories/Samples.v`.
- **Env effect** (breadth iteration 2): `OAsk` reads a read-only context threaded as a `ctx`
  parameter of `run`; `theories/Env.v` proves `ask` reads the context, the idempotence law
  `ask ;; ask = ask`, a concrete landing, and an ignore-the-context mutant (axiom-free).
  `runtime/env.ml` is the `Effect.Deep` handler; `tests/diff_env.ml` checks the context flows
  identically over 3000 states. Effects now compose three-deep (Env ∘ Error ∘ KV).
- **`world` refactor + Trace effect** (breadth iteration 3): `run` now threads a single `world`
  record `{ kv; ctx; trace }` instead of separate parameters, so adding an effect adds a FIELD, not a
  `run` parameter. The KV/Error/Env proofs were re-proved over `world` (still axiom-free). `OTrace`
  appends to `world.trace`; `theories/Trace.v` proves `sample_trace_records` (events in order) + an
  order-matters mutant; `runtime/trace.ml` is the buffer handler; `tests/diff_trace.ml` checks the log
  + state over 3000 states. Effects now compose four-deep (Trace ∘ Env ∘ Error ∘ KV).
- **Cache effect** (breadth iteration 4): `OCacheGet`/`OCachePut` over a `world.cache` field kept OUT
  of `observe` (observationally invisible). `theories/Cache.v` proves `cache_invisible` (a correct HIT and
  a MISS give the same KV result) plus `run_cache_uses_value` (the cached value is genuinely read, so the
  invisibility is non-trivial) — axiom-free. `runtime/cache.ml` is a separate Hashtbl handler;
  `tests/diff_cache.ml` is metamorphic (reference == fast-miss == fast-hit, 3000 states). This completes
  the report's five-effect MVP family (State, Error, Env, Trace, Cache).
- **Recursion** (breadth iteration 5): `tm` gains `Repeat n body` (a bounded loop = the report's
  `for_i`/fuel recursion); `run` interprets it with a fuel-structural inner fixpoint; codegen lowers it to a
  native `for` loop. `theories/Recur.v` proves the loop invariant **by induction** (`repeat_incr_present`)
  and `sample_count_correct` (5 increments ⇒ key 0 = 5) — axiom-free; the first proof reasoning about
  recursion. `sample_count` is in the KV adversarial harness (`diff_kv`, now 7 programs). This checks the
  last MVP-acceptance box ("simple recursion").
- **Error effect** (breadth iteration 1): `OThrow` aborts the computation; `theories/Error.v` proves the
  algebraic law `throw e ;; k = throw e`, a concrete abort (`sample_throw_aborts`), and a no-throw mutant —
  all axiom-free. `runtime/err.ml` is the native-exception backend (`throw`/`run_error`); `tests/diff_err.ml`
  checks outcome AND state over 3000 states (both throw/return paths).
- **Proofs** (`theories/KV.v`, all `Qed`, `Print Assumptions incr_correct` = "Closed under the global
  context"): `incr_correct` with a **frame clause**; the three P7 state laws (`find_add_same`, `put_put`,
  `get_get`); three anti-vacuity artifacts (`incr_spec_inhabited`, `incr_wrong_rejected`, `incr_clobber_rejected`).
- **Bridge**: `extraction/` → `ref_extracted` library (Obj.magic-free); `codegen/` lowers the **extracted ADT
  directly** to direct-style OCaml; `runtime/kv.ml` deep handler; `tests/diff_kv.ml` = 6 programs × 5000
  adversarial states = 30000 comparisons, 0 fails, coverage T2/T4/T5 asserted, T8 (both arms).
- **Trust artifacts**: `docs/runtime_manifest.toml`, generated `docs/tcb_report.md`, 6 CI gates.

## Divergences from the spec files (read these alongside the spec)
- **[[effir]]** lists `VPrim prim (list val)` and a general `Match val (list branch)` with an exhaustiveness
  `typecheck_ir.ml`. Slice 1 implements **`VZero`/`VSucc`** (the only prims) instead of `VPrim`, and
  **`MatchOpt`** (option-only) instead of general `Match`; there is **no `typecheck_ir.ml`** — the reduced
  inductive *cannot represent* out-of-fragment terms, so the OCaml match in the codegen is exhaustive by
  construction. The extracted ADT is renamed/multi-module (`coq_val`, `coq_Z`, Peano `nat`, …).
- **[[codegen]]** describes emitting `<prog>_effects.ml/.mli` + `_handlers.ml/.mli` with manifest/contract
  **hashes**. Slice 1 emits **one** `prog0_generated.ml` containing all programs; the effect declaration +
  curried wrappers + deep handler are **hand-written** in `runtime/kv.ml` (a reviewed realizer); there is **no
  hash header** — freshness is a **regenerate-and-`git diff`** gate (`ci/check_generated_fresh.sh`), not a
  hash. The codegen consumes the extracted ADT directly (no hand-written mirror) and names binders by de
  Bruijn depth (no global state).
- **[[runtime-manifest]]** / **[[adr-0004-trust-model]]**: the refinement is a **documented manifest
  assumption** (`Runtime_KV_refines` in `docs/runtime_manifest.toml`), **not a Rocq `Axiom`** — so the Rocq
  development stays axiom-free. Manifest **rule 1** (codegen resolves prim/op names against the manifest) is
  **not yet enforced** in code: slice-1 prims (`Z.zero`/`Z.succ`) and KV ops are inlined in `codegen.ml`.
  The assumption is validated for the **6 programs** over adversarial states, not literally "all programs".
- **[[error-taxonomy]]**: the five named codegen error codes are mostly **statically unreachable** in slice 1
  (the reduced ADT has no constructors for unsupported/cofix/cast cases); the live failures are the two
  arity/scope `Codegen_error` cases. `run_checked` returns the typed `` `Unhandled_effect ``/`` `Unexpected_exception `` variants (2 arms; the spec's `Runtime_error` arm lands with the `ErrorE` effect, post-slice).
- **[[conv-error-handling]]**: slice-1 `run_checked` has 2 arms (Unhandled + Unexpected); the 3rd
  (`ErrorE`/`Runtime_error`) arrives with the Error effect in breadth.

## Deferred to breadth (post-slice, by design)
General `Match`/`VPrim` + `typecheck_ir.ml`; generated effects/handlers modules + hash headers; manifest-driven
prim resolution; abstract `TNamed` realization; recursion; GADT witnesses;
the codec pilot. (`Error`, `Env`, `Trace` are now built — see above.)

## Agent notes
> Do not "fix" the code to match the aspirational spec clauses above — they are deliberately deferred. If you
> extend the fragment (e.g. add general `Match`), update [[effir]] and delete the corresponding row here.

## Related files
- `plan.md` — the slice plan and the resolutions these divergences trace to.
- `properties/functional.md` — the P-entries now established (P5 tested over 6 programs).
</content>
