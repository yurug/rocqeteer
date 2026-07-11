# Session state — Rocqeteer

_Last updated: 2026-07-11_

## What this project is
A domain-independent trusted toolchain to use Rocq as a certified programming language: write effectful
programs in Rocq, prove them against reference semantics, generate fast idiomatic OCaml 5, with a small
explicit TCB. Based on `rocq_effectful_extraction_report.md`, built via the `agentic-dev-kit/` spec-driven
methodology. **Read `CLAUDE.md` and `kb/INDEX.md` first.**

## Methodology progress
- ✅ **Phase 0 — Orient.** Fresh project; toolchain verified (Rocq 9.1.1, OCaml 5.4.1, dune 3.23.0, qcheck, zarith). Git initialized.
- ✅ **Phase 0.5 — Premortem.** 7 failure modes; artifacts in `kb/reports/premortem-idea-20260620.{md,html}`.
- ✅ **Phase 1 — Ambiguity resolution.** `kb/questions-round1.md`. Outcome: **all defaults accepted; non-functional = MEASURE, not prove.** (Project is independent of Tezos/Octez — corrected mid-session.)
- ✅ **Phase 2 — Knowledge Base.** 34 content/index files under `kb/`. Structural audit clean (35 ids, links resolve). KB quiz (`kb/reports/kb-quiz-round1.md`) scored **10/10**, no material gaps. Committed.
- ✅ **Phase 3 — Planning.** `kb/plan.md` drafted (3-step KV slice, risk-ordered). Plan-simulation gate passed (it compiled extraction + effects on the live toolchain); **7 resolutions** folded into the plan and the KB (`kb/reports/plan-simulation-round1.md`). **Awaiting user approval** (Phase 3 exit). Plan + KB refinements are **uncommitted** pending approval.
- 🔄 **Phase 4 — Implementation (in progress).**
  - ✅ **Step 1 (bridge spike)** — commit `880401a`. One extracted EffIR `prog0` drives both the reference interpreter and the generated direct-style OCaml; differential `{7→1}` green. `make smoke`/`test`/`ci-checks` pass. Codegen consumes the extracted ADT directly (no mirror to drift).
  - ✅ **Step 2 (proven incr)** — `theories/KV.v`: `incr_correct` proven (Print Assumptions = "Closed under the global context", no axioms), state laws P7, inhabitance lemma + `incr_wrong_rejected` mutant. The `Dstuck` cases fell out of the precondition — no well-typed-view needed.
  - ✅ **Step 3 (harden)** — adversarial differential test `tests/diff_kv.ml` (5000 cases, 0 fails, coverage T2/T4/T5 asserted, T8 fault injection); generated file promoted+committed with a freshness gate; `docs/runtime_manifest.toml` + generated `docs/tcb_report.md`; 6 CI gates (`make all` green). **Slice DoD met → breadth unlocked** (green end-to-end examples = 1).

- ✅ **Phase 5 — Quality audits.** 3 independent audit agents (test-gap/provability, spec-compliance/simplicity, security/TCB). All criticals/highs fixed: `run_checked` catches all exceptions + typed errors; `runtime/kv.mli` (+coqconv/fault) hides effect constructors; `incr_spec` frame clause + clobber mutant; **multi-program differential** (Samples.v: ODelete/Ret/multi-Perform/neg-key/deep-nesting) → 6 progs × 5000 states; codegen depth-naming (no global ref); CI hardening (scan generated/, broader axiom grep, pos_of_z guard, ci-checks⊇test). Commit `b17d64e`.
- ✅ **Phase 6 — KB sync.** `kb/spec/slice1-status.md` (authoritative built-vs-spec) + banners on divergent specs; `get_get` P7 law proven; sync-quiz 3/3. Commit `abcbff0`.
- ✅ **Phase 7 — Docs & validation.** `README.md` (workflow = the validation); clean `make all` green from scratch.

**The full methodology (Phases 0–7) is COMPLETE for the KV slice.** `make all` green on Rocq 9.1.1 / OCaml 5.4.1.

## Key decisions locked (see ADRs)
1. One first-order **EffIR** shared by reference interpreter and codegen; no HOAS `Prog`. (adr-0001)
2. EffIR → codegen via Rocq **extraction to an OCaml ADT**; no JSON in the TCB. (adr-0002)
3. v1 deps = **rocq-stdlib + qcheck + zarith only**. (adr-0003)
4. **Prove functional, measure non-functional**; every refinement axiom named in the TCB report. (adr-0004)
5. **Anti-vacuity**: inhabitance lemma + proof-mutation test per spec. (adr-0005)
6. **Vertical slice first**: KV green end-to-end before any breadth. (adr-0006)

## Breadth iterations
- ✅ **Iteration 1 — `Error` effect (`OThrow`).** `run` returns `outcome * state` with `Bind` short-circuit;
  `theories/Error.v` (law + abort + mutant, axiom-free); `runtime/err.ml`; `tests/diff_err.ml`.
- ✅ **Iteration 2 — `Env` effect (`OAsk`).** read-only `ctx`; `theories/Env.v` (laws + mutant, axiom-free);
  `runtime/env.ml`; `tests/diff_env.ml`. Three-deep (Env ∘ Error ∘ KV).
- ✅ **Iteration 3 — `world` refactor + `Trace` effect (`OTrace`).** `run` threads one `world` record
  `{ kv; ctx; trace }`; future effects add a FIELD. `theories/Trace.v` (order law + mutant);
  `runtime/trace.ml`; `tests/diff_trace.ml`. All diff tests use one `observe_full` entry point.
- ✅ **Iteration 4 — `Cache` effect (`OCacheGet`/`OCachePut`).** Added as a `world.cache` FIELD (the refactor
  paying off) kept OUT of `observe`. `theories/Cache.v`: `cache_invisible` (hit ≡ miss) + `run_cache_uses_value`
  (anti-vacuity), axiom-free. `runtime/cache.ml` Hashtbl handler; `tests/diff_cache.ml` metamorphic
  (reference == fast-miss == fast-hit). **Completes the report's five-effect MVP family** (State, Error, Env,
  Trace, Cache), all composed, all axiom-free, all differentially tested. `make all` green.

## Exact next step
The five-effect MVP family, bounded recursion, and the GADT codec pilot are all done (iterations 1-6 below).
`make all` green. Natural next options (none started):
1. **General `Match`/`VPrim` + an IR typechecker** — the remaining EffIR fragment expansion (update [[effir]]
   + [[slice1-status]] when done).
2. **Generated effect/handler modules + hash-headed generated files** — close the codegen-vs-spec gap.
3. **Abstract `TNamed` type realization** via the manifest (currently slice-1 uses concrete `Z`).
4. **Mode B** (recognized monadic Gallina via MetaRocq) — blocked until MetaRocq is packaged for Rocq 9.x.

## Breadth iterations (all committed, all `make all` green)
- ✅ 1 `Error` (`OThrow`); ✅ 2 `Env` (`OAsk`); ✅ 3 `world` refactor + `Trace` (`OTrace`);
  ✅ 4 `Cache` (`OCacheGet`/`OCachePut`, observationally invisible) — completes the five-effect MVP family.
- ✅ 5 **Recursion** (`Repeat`, proven by induction; closes the MVP "simple recursion" box).
- ✅ tooling: single-source `Samples.all_programs` (extracted + iterated by codegen).
- ✅ 6 **Codec pilot** (GADT witnesses): proven round-trip in `theories/Codec.v` + GADT/`bytes` realizer
  (no unsafe casts), property-tested. The realistic A3 target.

✅ **Demo** (`make demo`): the composed `demo_prog` (Env+Trace+recursion+KV) shown end-to-end — Rocq
source + proven theorem (`theories/Demo.v`, vm_compute) → generated OCaml → live run → reference==fast →
codec round-trip; narrated CLI + `demo/demo_report.html`.

Effects compose; every effect/feature is proven axiom-free in Rocq and differentially/property tested.
Deferred design items: `kb/spec/slice1-status.md` ("Deferred to breadth").

## Open / deferred
- Exact EffIR Rocq constructor names: pinned during slice-1 implementation (intentional deferral).
- Repo remote (private GitHub): create only when the user asks (E2). No push yet.
- Mode B (monadic Gallina via MetaRocq), ITree bridge, GADT witnesses, Error/Env/Trace/Cache effects, codec
  pilot: all post-slice-1.

## Interleaved consumer: verdis (R0 done 2026-07-10)
verdis (~/work/dev/verdis) drives IR v2 (its kb/external/rocqeteer.md holds requirements R0-R10 per its
ADR-0002 — no timebox, user decision). R0 = this packaging commit: `rocqeteer.opam` (generate_opam_files),
theory installable to user-contrib (package rocqeteer), codegen public as `rocqeteer-codegen`. Verified:
dune install → 35 files incl. Rocqeteer/*.vo + bin/rocqeteer-codegen; make all green. IR v2 MILESTONE 1 DONE (2026-07-10): runtime value universe
generalized — new runtime/rval.ml(+mli) mirrors dval 1:1 (Unit/Bool/Int/None/Some/Pair; Dstuck = exception
Stuck, not a constructor); all value-carrying handlers (Kv/Env/Trace/Cache/Err) + observables + all 7 diff
suites + codegen + demo retyped to Rval.t; ZERO theories/ changes, make all + make demo green from clean.
Design notes: Kv.get/Cache.get return Rval.t encoding option via opt_to_rval (mirrors reference
opt_to_dval); emit_key separate from emit_val (keys stay Z.t); check_generated_fresh.sh now diffs source
vs build artifact (same CI intent, no mid-dev chicken-and-egg). R1 VBYTES DONE (2026-07-10, 4bdc26b): DBytes/VBytes through
every layer; BytesVal.v proven axiom-free (+inhabitance+mutation); diff_bytes adversarial suite (NUL/CRLF/
high-bytes/large classes); Runtime_Bytes_refines in the manifest; 8 proofs closed; make all+demo green.
R2 GENERAL MATCH DONE (2026-07-10): ADR-0008 designed then implemented —
pat (literals + PNone/PSome/PPair), first-match-wins + mandatory default, MatchOpt removed, 9 sites
migrated, Dispatch.v (6 theorems incl. duplicate-branch first-match-wins observability), chained codegen,
diff_dispatch suite. 14 proofs closed; make all + demo green.
R3 VPRIM DONE (2026-07-11, 0640bbf): ADR-0009 implemented — prim inductive (9 prims), TOTAL apply_prim
(mismatch -> DNone), strict int64 parse/print DP1-DP8 ("-0" rejected, matches verdis Q-INT-PARSE),
Prim term as a pure run step; theories/Prims.v 30+ closed theorems (round-trip at 0/±1/max/min,
per-class rejection lemmas, sample_parse ERR/OVF paths, inhabitance, lenient mutant); realizers in
runtime/prims.ml written from the Rocq defs; diff_prims = 3000 pipeline states (G1-G16, coverage
asserted) + 2000-round direct apply_prim-vs-realizer pass over all 9 prims. All CI gates green
post-commit; make demo green. Two fixes made during verification of the delegated implementation:
(a) prim_bytes_sub bounds-checked in Z BEFORE Z.to_int (2^70 offset raised Z.Overflow — escaping
exception from a raises=[] realizer); (b) PROOF-ENGINEERING TRAP, remember this: `eexists. split;
vm_compute` runs vm_compute on the second conjunct while the witness evar is uninstantiated — VM
compilation of the open term ballooned to 42 GB and the kernel OOM-killed the build. Always give
explicit witnesses before vm_compute on multi-conjunct existential goals.
Next milestones: R7 reply ADT (structured RESP-value type expressible in the IR) — then verdis step 2
(proven RESP2 codec in the live path). Remaining v2 backlog: R4 expiring store, R5 Time, R6 lists,
R8 message errors, R9 journal, R10 typechecker.
