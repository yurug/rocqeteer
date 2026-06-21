---
id: plan
type: procedure
summary: Three-step implementation plan for the KV vertical slice — bridge spike first (riskiest), then the proven incr, then the hardened adversarial differential slice — risk-ordered, each with its single biggest unknown, refined by the plan-simulation gate.
domain: planning
last-updated: 2026-06-20
depends-on: [prd, arch-overview, effir, adr-0001-first-order-ast, adr-0002-extraction-bridge, adr-0006-vertical-slice]
refines: []
related: [reference-semantics, codegen, conv-testing-strategy, runbook-build-validate]
---
# Plan — KV vertical slice (v1, slice 1)

## Goal of the slice
Carry **one** effect (KV) end-to-end so the core mechanism is proven on the smallest real example:
EffIR `incr` -> proof against reference semantics -> extraction -> codegen -> fast OCaml + deep handler ->
adversarial differential test green. This unlocks "breadth" ([[adr-0006-vertical-slice]]). Three steps; the
quality audit (Phase 5) is separate.

## Foundational representation decision (settled, drives every step)
EffIR's Rocq datatype is **extrinsically typed**: plain first-order inductives `ty`, `dval` (runtime
values), `val`, `op`, `tm` with **no type indices in constructors**, so extraction emits an `Obj.magic`-free
OCaml ADT ([[adr-0002-extraction-bridge]], [[ext-rocq-extraction]]). Well-typedness/scoping is a *separate*
predicate (Rocq `Prop` for proofs; `typecheck_ir.ml` on the OCaml side). The reference interpreter is
**total**, producing `dval`, with a **`Dstuck` sentinel** on impossible cases that proofs discharge as
unreachable for well-typed closed terms. See [[effir]], [[reference-semantics]].

## Resolutions from the plan-simulation gate (round 1)
A fresh subagent simulated this plan against the KB and the **live toolchain** (it ran `coqc`/`Separate
Extraction` and OCaml 5.4.1 effects to verify). Core bets held: first-order extraction is `Obj.magic`-free
and the effect syntax compiles. Seven items resolved (full report: `reports/plan-simulation-round1.md`):

1. **dune Rocq integration:** use `(using rocq 0.13)` — `(rocq.theory ...)` for libraries plus a *separate*
   `(rocq.extraction (prelude ...) (extracted_files ...) (theories ... Stdlib))`; the prelude `.v` is
   excluded from any theory stanza; every extracted `.ml/.mli` is listed explicitly. (The `coq.*` stanzas
   are removed in dune 3.24.) Verified working here.
2. **Interpreter totality:** `run` is **total**, returning `dval * state` with a **`Dstuck` sentinel** (not
   `option`) — `verifies` destructures a total pair. A small "well-typed closed term" view supplies the
   lemmas that discharge `Dstuck` as unreachable — a guaranteed Step-2 build item, not a contingency.
3. **Slice-1 types are concrete:** `key = value = TInt` (Rocq `Z`, realized to `Zarith.Z.t`), so
   `value_succ = Z.succ` is well-typed and the reference map is `FMapAVL` over `Z_as_OT`. Abstract `TNamed`
   realization is deferred to the codec pilot (`value_succ`/`value_zero` still exercise the prim manifest).
4. **Extraction is faithful & multi-module:** the extracted ADT is renamed (`coq_val`, `coq_Z`, Peano `nat`,
   inductive `string`/`ascii`) across several files (`EffIR`, `BinNums`, `Datatypes`, ...), all
   `Obj.magic`-free. The only `Extract` mappings are manifest-registered realizers (`Z -> Zarith.Z.t`). The
   `codegen/eff_ir.ml` mirror reflects this real shape; the sync check is a **`.mli` diff**, not a grep.
5. **Normalizer/observable is a Step-1 deliverable:** a canonical-bindings function (sorted `(key,value)`
   list, `coq_Z -> Zarith.Z` on both sides) over the extracted `FMapAVL` state and the OCaml `Hashtbl`; it
   defines `observable`/`run_spec_KV`/`run_fast_KV` named in the `Runtime_KV_refines` manifest entry.
6. **T-class coverage is asserted, not assumed:** Step-3 acceptance requires logged QCheck coverage counts
   > 0 for **T2/T5/T6/T7**. **T1 (overflow) is N/A in slice 1** (`Z` cannot overflow; no `int63` realizer
   yet) — dropped from the slice DoD.
7. **Effect arity convention:** tupled constructor (`Put : key*value -> unit Effect.t`) + curried public
   wrapper (`put : key -> value -> unit`); codegen lowers `Perform (KV,Put) [k;v]` through the wrapper.

Process: prefer in-file `Fail Theorem`/`Fail Lemma` for the anti-vacuity mutant (machine-checked in `make
rocq`). Steps 2-3 keep a **human checkpoint** (P6 statement review; `tcb_report.md` diff) — they do not
fully self-close in the Ralph loop.

---

## Step 1 — Bridge spike: smallest program, running end-to-end (RISKIEST FIRST)
**Why first:** the make-or-break is whether *one* EffIR value can drive both the extracted reference
interpreter and the codegen. Settle it on the smallest term before writing `incr` or any proof.

**Build:**
- Dune workspace (`theories/`, `codegen/`, `runtime/`, `tests/`) using `(using rocq 0.13)` (Resolution 1) +
  the `make smoke` day-zero gate: deps build, OCaml 5.4.1 `perform`/`Effect.Deep`/`match…with effect`
  compile, **and an extraction round-trip succeeds**. [[runbook-build-validate]], [[adr-0003-dependency-budget]]
- EffIR inductives (extrinsic, as above) + KV `op`s + a total reference `run` (with `Dstuck`) and the KV
  handler over `FMapAVL` (`Z_as_OT`). [[effir]], [[reference-semantics]]
- A small term `prog0` (a reduced `incr`: one `Bind`, one `Perform Get`, one `Match`) — enough to exercise
  all four `tm` forms the codegen must lower.
- `theories/Extraction`: `Separate Extraction` of `tm`/`val`/`dval` + `prog0` + `run`, wired via
  `(rocq.extraction …)` with the explicit `extracted_files` list (Resolution 1).
- `codegen/eff_ir.ml` mirroring the **renamed multi-module** extracted shape (Resolution 4); minimal codegen
  consuming the extracted `tm` ADT, emitting direct-style OCaml for the four forms.
- The **normalizer** (sorted `(key,value)` bindings, `coq_Z`↔`Zarith` bridge) over the extracted `FMapAVL`
  state and an OCaml `Hashtbl`; it is the shared `observable` (Resolution 5).
- `runtime/`: a KV deep handler over `Hashtbl`, resuming each continuation once. [[ext-ocaml5-effects]]
- Run generated `prog0` under the handler; run extracted reference `run prog0`; compare via the normalizer.

**Observable progress:** a tiny KV program produces identical observable results via reference and fast.

**Acceptance:** `make smoke` green (incl. the extraction round-trip) · extracted EffIR ADT is
**`Obj.magic`-free** (grep) and **`.mli`-diffs** clean against the `codegen/eff_ir.ml` mirror (accounting for
the `coq_`-prefixed multi-module shape) · generated output has **no `Bind`/free-monad constructor** (P3) ·
reference == fast on `prog0` via the normalizer.

**Biggest unknown:** the cast question is *settled* (the gate verified extraction is `Obj.magic`-free). The
real risk is plumbing: the renamed **multi-module** extracted shape, the `FMapAVL`↔`Hashtbl` **normalizer**,
and the `(rocq.extraction extracted_files …)` wiring. The spike targets those. If the extracted shape proves
unusable for the codegen mirror, **stop and re-plan the EffIR representation here** — the discovery this
ordering forces early.

---

## Step 2 — `incr` proven against reference semantics, non-vacuously
**Why second:** the proof is comparatively routine once the bridge works; do it before hardening.

**Build:**
- `incr` as an EffIR term (`Get k`; match; `Put k (value_succ …)`) with slice-1 `key = value = Z` (concrete
  `TInt`, Resolution 3); register pure prims `value_zero = Z.zero` / `value_succ = Z.succ`. [[runtime-manifest]], [[ext-zarith]]
- A small **well-typed closed-term view** + lemmas discharging the `Dstuck` sentinel as unreachable (Resolution 2).
- Prove KV state laws (P7) and `incr_spec` (P-functional) over the reference handler — **no `Admitted`**.
- **Anti-vacuity companions** ([[adr-0005-anti-vacuity]]): an inhabitance lemma `∃ s, pre s`, and an in-file
  `Fail Theorem` mutant — a wrong `incr'` (e.g. one that writes `value_zero`) for which `incr_spec` is
  **un**provable. [[conv-testing-strategy]]
- `Print Assumptions incr_spec` captured into `tcb_report.md`.

**Observable progress:** `incr` has a machine-checked, demonstrably non-trivial spec.

**Acceptance:** `incr_spec` + state laws proven · inhabitance lemma proven · the `Fail` mutant confirms the
spec rejects a wrong impl · `Print Assumptions` shows no unexpected axioms · **human review** confirms
`pre`/`post` are meaningful (P6).

**Biggest unknown:** *does the extrinsically-typed, total interpreter allow clean Hoare proofs about `incr`
without drowning in `Dstuck`/well-typedness side conditions?* The well-typed closed-term view exists to
discharge those once and reuse; if it does not tame them, reconsider the interpreter's return shape before Step 3.

---

## Step 3 — Hardened slice: full codegen, refinement axiom, adversarial differential test (SLICE DoD)
**Why last:** hardening and the trust artifacts build on a working, proven core.

**Build:**
- Codegen emits the full file set: `<prog>_effects.ml/.mli` (`type _ Effect.t += …` tupled constructors +
  curried private `perform` wrappers, Resolution 7), `<prog>_generated.ml/.mli` (direct-style `incr`),
  hash-headed "do not edit" headers, deterministic formatting. [[codegen]], [[effect-signatures]]
- `runtime/`: checked entrypoint wrapper converting `Effect.Unhandled`/stray exceptions to typed results
  (T8). [[conv-error-handling]]
- Register the `Runtime_KV_refines` axiom (naming `run_spec_KV`/`run_fast_KV`/`observable`) in the manifest +
  `tcb_report.md` (review-labeled). [[adr-0004-trust-model]], [[runtime-manifest]]
- Differential test: QCheck generators **biased** toward T2 (missing key), T5 (duplicate `Put`), T4 (large
  state), T6 (collisions), T7 (order-independence) over random states/keys, with **logged coverage counts
  > 0** per class (Resolution 6); **seed logging**; counterexamples persisted to `tests/corpus/`. T1
  (overflow) is **N/A in slice 1**. Fault injection: unhandled effect -> typed error (T8). [[conv-testing-strategy]], [[ext-qcheck]], [[prop-edge-cases]]
- Wire CI gates: no-`Bind` grep, generated-hash check, no-stray-`perform`, no-`Admitted`, `tcb_report.md`
  diff, public-entrypoint-has-differential-test. [[error-taxonomy]], [[runbook-build-validate]]

**Observable progress:** the full pipeline (`make rocq -> extract-ref -> gen-fast -> build-fast -> test ->
tcb-report`) runs green on adversarial inputs.

**Acceptance (slice definition of done, [[runbook-build-validate]]):** generated `incr` is idiomatic
direct-style (no `Bind`) · `build-fast` type-checks on 5.4.1 (P4) · KV differential green with **logged
coverage > 0 for T2/T5/T6/T7** (T1 N/A — no `int63` in slice 1) (P5) · `tcb_report.md` lists
`Runtime_KV_refines` + `value_succ` · CI gates active · "green end-to-end examples" counter = **1** ->
breadth unlocked.

**Biggest unknown:** *will the `Z`/`FMapAVL` reference and the `Hashtbl`/OCaml fast side agree under
adversarial inputs?* With `Z` as default the live divergence sources are **iteration order (T7)** and the
**`FMapAVL`↔`Hashtbl` observable mapping (T6)** — normalizer correctness, not arithmetic. A divergence here
is a **success of the method** (caught pre-production): fix the realizer/normalizer, add a corpus entry, re-run.

---

## Out of this slice (next invocations, post-green)
Error/Env/Trace/Cache effects · recursion in EffIR · GADT witnesses · the codec pilot · Mode B / MetaRocq ·
ITree bridge · abstract `TNamed` type realization · benchmarks beyond a smoke. None begins before Step 3 is
green ([[adr-0006-vertical-slice]]).

## Ralph-loop note
One fresh subagent per step, ≤7 iterations; if a step will not converge, stop and split it — do **not** pivot
to easier modules while the step's named unknown is unresolved. Steps 2-3 include a human checkpoint
(Resolution process note) and so are not fully autonomous.

## Related files
- `runbooks/build-and-validate.md` — the exact pipeline commands and gates each step targets.
- `properties/functional.md` / `edge-cases.md` — the P/T ids in the acceptance criteria.
- `reports/premortem-idea-20260620.md` — the failures this risk-ordering defends against (#1, #3, #5, #6).
- `reports/plan-simulation-round1.md` — the gate findings these resolutions close.
</content>
