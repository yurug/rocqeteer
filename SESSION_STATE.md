# Session state — Rocqeteer

_Last updated: 2026-06-20_

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

**Phase 4 (the requested Steps 1–3) is COMPLETE.** `make all` is green on Rocq 9.1.1 / OCaml 5.4.1.

## Key decisions locked (see ADRs)
1. One first-order **EffIR** shared by reference interpreter and codegen; no HOAS `Prog`. (adr-0001)
2. EffIR → codegen via Rocq **extraction to an OCaml ADT**; no JSON in the TCB. (adr-0002)
3. v1 deps = **rocq-stdlib + qcheck + zarith only**. (adr-0003)
4. **Prove functional, measure non-functional**; every refinement axiom named in the TCB report. (adr-0004)
5. **Anti-vacuity**: inhabitance lemma + proof-mutation test per spec. (adr-0005)
6. **Vertical slice first**: KV green end-to-end before any breadth. (adr-0006)

## Exact next step
Steps 1–3 are done and committed; `make all` green. Remaining methodology phases (not yet started):
- **Phase 5 — Quality audits** (test-gap, anti-vacuity, security, perf, spec-compliance, simplicity, TCB).
- **Phase 6 — KB sync**: reconcile the KB with what was built. Known divergences to fold in: codegen
  consumes the extracted ADT directly (no hand-written mirror); the refinement is a *documented manifest
  assumption*, not a Rocq `Axiom` (so Rocq stays axiom-free); slice-1 uses `MatchOpt` (option-only) as the
  match form; slice-1 `key=value=Z` concrete; no well-typed-view was needed.
- **Phase 7 — Docs** (README, user manual).
- **Breadth** (post-slice): Error/Env/Trace/Cache effects, recursion, GADT witnesses, codec pilot.

## Open / deferred
- Exact EffIR Rocq constructor names: pinned during slice-1 implementation (intentional deferral).
- Repo remote (private GitHub): create only when the user asks (E2). No push yet.
- Mode B (monadic Gallina via MetaRocq), ITree bridge, GADT witnesses, Error/Env/Trace/Cache effects, codec
  pilot: all post-slice-1.
</content>
