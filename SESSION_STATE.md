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

## IR v2 CONTRACT COMPLETE (2026-07-12): R0-R10 all landed
Night run 2026-07-11/12 (user authorized autonomous overnight work): R4+R5 (5593f78, ADR-0011 — Time +
expiring store, boundary now<=d validated by verdis's 12,500-case oracle run), R6 (6880e61, ADR-0012 —
Fold + PListLen/PListNth/PMulChecked; R8 confirmed closed with payload-pinning theorems), R9 (093a39a,
ADR-0013 — Journal with the frame law and run-sequence composition lemma PROVEN GENERAL; + PDivFloor
range-checked), R10 v1 (9dec025, ADR-0014 — wf checker with GENERAL soundness: run_checked = Some . run
for wf programs, scope-Dstuck class dead; codegen wf-gates every program; emission core exposed as
public library rocqeteer.codegen + rocqeteer.{extracted,coqconv,runtime} for consumers). R11 remains
NOT NEEDED (spike V). Every verdis requirement row R0-R10 is green. Pattern held: ADR first, sonnet
execution agents, from-clean verification + trust-diff review before every commit; two spec bugs caught
in review (PDivFloor range check, base-unix invariant-2 declaration). Deferred: R10 phase 2 (value-shape
typing — open design question: how consumer tag->payload shapes are declared), demo does not yet show
Fold/Journal/Time (demo refresh when next presenting).

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
R7 STRUCTURED VALUES DONE (2026-07-11, ADR-0010 + f0cf865): DTag (Z-tagged sums) + DList (values only,
NO elimination until R6) + PTag depth-1 pattern; Rval.Tag/List + coqconv bridge + codegen (when-guard
literal-tag match); StructVal.v 11 closed theorems (tag-collision observability, swapped-tags mutant,
wrong-tag/non-tag fall-to-default); diff_structval (5000 sample states + 2000 fuzzed bridge round-trips,
coverage asserted). Design note: R7 stays domain-neutral — the consumer defines its ADT (e.g. RESP reply)
in ITS theories with a proven of_dval/to_dval round-trip; RESP never enters rocqeteer. R7 also delivered
R6's value half; R6 shrinks to list ELIMINATION only (pattern or bounded fold).

GENERAL ROUND-TRIP (2026-07-11, 93ffc86): parse_print_roundtrip proven for ALL in-range z (closes the R3
documented deferral; print_digits_fuel_spec fuel-induction + apply_parse_int64 walk lemmas; TCB report
captures it). Downstream driver: verdis RESP2 codec's RInt case.

**IR v2 verdis-step-2 precondition (R0+R1+R2+R3+R7) is COMPLETE.** Next: verdis step 2 (proven RESP2
codec in the live path, in the verdis repo — pin bump to f0cf865 needed in verdis ci/rocqeteer.lock).
Remaining v2 backlog (step-3 drivers): R6 list elimination, R8 message errors, R9 journal, R10 typechecker.

R4+R5 TIME + EXPIRING STORE IMPLEMENTED (2026-07-11, ADR-0011, UNCOMMITTED — awaiting review):
Z-keyed KV REPLACED by bytes-keyed expiring store — M = FMapAVL(String_as_OT), entry = (dval * option Z),
world gains now_ms (immutable per run), ops OGet/OPut/ODelete re-shaped + OGetDeadline/OSetDeadline/ONow;
liveness = now <=? d (alive AT deadline — oracle-validated boundary; malformed args stay Dstuck);
observe filters expired and returns entries. run_top ctx now t. theories/TimeStore.v: 21 closed
theorems (boundary d/d+1, put-clears, persist, setdl-missing, ONow+PAddChecked at 0/negative/overflow,
full local mutant interpreter with `<` liveness observably rejected, deadline-state inhabitance).
incr_correct re-proven over the store for EVERY now (live view; put pins deadline None) + deadline-
carrying inhabitant. Cache keys migrated to bytes too (one emit_key discipline). runtime/: time.ml
(source = unit -> Z.t, wall_clock_ms via Unix — base-unix declared, ships with compiler), kv.ml
bytes-keyed (Rval.t * Z option) Hashtbl with lazy expiry, runtime.ml = Runtime.with_store_and_time
(ONE source, Time outermost; manifest assumption Runtime_SingleTimeSource_refines). codegen: bytes
emit_key + new op lowerings; all store ops return Rval.t. Samples: decimal-bytes keys + sample_store/
ttl/put_clears/persist/setdl_missing/now. Tests: 11 suites migrated + diff_store (3000 states, boundary
d-1/d/d+1 asserted per key, NUL/prefix-collision/empty keys, coverage K/D/P asserted) + diff_time
(3000 runs, 0/negative/2^62/overflow, reference-now == fast-source-now). make all green except the
expected check_tcb git-drift FAIL (tcb_report.md regenerated, uncommitted); make demo green;
kb-lint clean; 67 Print Assumptions all "Closed under the global context".

## 2026-07-18 — public README: effects list + gallery (user request)
Repo is PUBLIC since 2026-07-17 (BSD-3, copyright Nomadic Labs). Added examples/ (RocqeteerGallery
theory, own dune, builds with make all): one proven demo file per effect family — KeyedStore, Expiry,
Clock, Throw, Ask, Tracing, Memo, Journaling, Combinators (27 vm_compute instance theorems, each file
header links to the general theory). examples/README.md = the gallery index. README.md gained "The
effects" table (12 ops / 8 families -> gallery links), status refreshed to IR v2 complete + first
consumer redoq, roadmap done-items corrected (Match/VPrim/Wf/Journal/Logic), license section fixed
MIT->BSD-3. make all green incl. gallery; pushed 3edfc70. Theorem count verified 413 (theories) + 27
(examples).

## 2026-07-19 — Phase C direction set: effect towers + application diversity (user design review)
User reviewed rocqeteer+redoq (voice memo, distilled into the ADR/plan; raw feedback.md left UNTRACKED
on purpose — personal memo, repo is public). Critiques: op set reads chosen-for-redoq (deadlines/cache/
journal are Redis features as primitives, contradicts domain-independence); TCB wide with no descent
path; low-level effect families missing; app diversity needed. Agreed resolution (user: "Let's do
this"): no vacuum redesign of primitives — instead the tower discipline. Artifacts committed:
- **ADR-0016 effect towers**: 7-op kernel (plain Store/Now/Throw/Ask/Trace) vs 5 derived ops
  (Expiry/Cache/Journal) discharged by total Rocq elaborations `elab_X : tm -> tm` + per-layer
  observational refinement theorems (no IR changes — invariant 1 intact); mode K (kernel-only
  execution of elaborated programs, CI-tested) beside mode F (fused, production); manifest/TCB report
  gain a `discharge` field per entry. Cache's elaboration is the NULL one (justified by the proven
  cache_invisible); Journal needs a reserved-key namespace wf extension (adr-0014).
- **kb/plan-towers.md** (phase-C roadmap): C1 tower mechanism + Expiry elaboration (flagship, hardest:
  lazy-expiry simulation through observe; wp-layer fallback authorized) → C2 Cache/Journal elabs +
  discharge column + README (the PRE-redoq-ANNOUNCEMENT item) → C3 Unix file tool (byte-stream fd I/O
  family, ADR-0017, differential vs coreutils) → C4 sequential HTTP server (sockets family) → C5
  concurrency (USER-FLAGGED priority; constraints fixed now: one-shot only, deterministic reference
  via schedule oracle in world, cooperative fibers+channels, recorded-schedule replay for diff tests;
  sequenced last because blocking ops from C3/C4 are the yield points). Compiler app REJECTED (user:
  purely functional compiler = CompCert territory, exercises no effects). Glossary + indexes updated;
  kb-lint 54 files 0 errors.

## 2026-07-19 — C1 DONE: the Expiry tower (ADR-0016) — proven, extracted, mode-K green
**theories/Elab.v** (~900 lines): `elab : tm -> tm` macro-expands the 5 expiry-surface ops into KERNEL
fragments (plain Get/Put/Delete + ONow; packed entries `DPair v dl` under never-expiring bindings).
Design keys that made it tractable: (1) bind-evaluated-args-once-at-db0 discipline — ZERO de Bruijn
shifting anywhere; (2) `Bind(Ret(VPair k dv))` + `Match PPair` to bind two args without shifts;
(3) is-an-int test = `Prim PCmpInt [x;x]` (DInt 0 iff int — total-prims trick); (4) setdl validates
the ARG SHAPE before the store lookup (handle_store's match order — Dstuck even on absent keys);
(5) Dstuck is producible as `VSucc VUnit`; passthrough of kernel Dstuck via `Ret (VVar n)`.
**THE THEOREM `elab_simulates`** (axiom-free, 12/12 Print Assumptions closed): ∀ t env w wk,
wrel w wk → same outcome + wrel preserved — NO wf side condition (malformed Dstucks reproduced
bit-for-bit). wrel = kv M.Equal-to-`M.map pack_entry` + all other fields equal (relation approach —
sidesteps AVL structural-eq of map∘add; FMapFacts pointwise lemmas only). Corollaries: run_top,
seeded (observe_full shape), observe-level (outcome/trace/journal EQUAL + find-pointwise store).
`wf_elab` (gate needs no special case) + boundary d-1/d/d+1 instances through elab + `<`-liveness
MUTANT elaboration rejected at the boundary (plausible away from it) + inhabitance witnesses +
`elab_all_programs_wf`. Proof-engineering traps hit (remember): Ltac `t1; t2; [a|b]` dispatch binds
to ALL goals in flight — parenthesize `(split; [a|b])` per-goal; cbn keeps `apply_cmp_int d d`
folded on abstract args (unfold + `Z.compare_refl`); `reflexivity` closes `M.Equal x x` via the
Equivalence instance (so `repeat split; reflexivity` proves wrel refl-instances).
**Mode-K pipeline**: Extr.v extracts `Elab.elab`+`elab_programs` (same names, elaborated bodies);
codegen `--elab` flag iterates the pre-elaborated list (NO elaboration logic in the trusted driver);
`generated/progk_generated.ml` (promoted, freshness-gated, wf-gated, 0 deadline-op calls);
`Kv.run_kernel` (+_checked/observe_kernel) = the ONLY new trusted code: plain table, no deadline
logic, NO clock, deadline ops UNHANDLED (loud). Manifest: Store gains `discharge =
derived(Elab.elab_simulates)`; new `Store_kernel` entry (kernel-v1); TCB report has the tower rows.
**tests/diff_store_k.ml**: same adversarial protocol as diff_store (seeded expiring states, boundary
instants, K/D/P coverage asserted) — reference(source, expiring) vs fast-K(elaborated, kernel);
packing/π in untrusted harness code. GREEN first run: 3000 states × 5 programs, 0 fails, boundary
asserted. From-clean `make all`: theory+extraction+codegen+17 test suites+demo green; all CI gates
pass (tcb drift = this commit's intended change). TCB: expiry semantics now PROVEN, not trusted —
the fused kv.ml realizer is a mode-F performance option.

## 2026-07-19 — C2 DONE: the consolidation tower (cache + journal + escaping) — mode K is FULLY kernel
Design CORRECTED at proof time (adr-0016 §Corrections, committed 80ac82e BEFORE implementation):
(1) null cache elaboration UNSOUND (put-then-get distinguishes — now the vm_compute mutant witness
mutant_cache_rejected); (2) syntactic reserved-namespace wf cannot bound runtime-computed keys →
TOTAL INJECTIVE KEY ESCAPING inside the elaboration: user keys "u"++k, cache "c"++k, journal "j" —
first-byte partition, collisions structurally impossible, theorems UNCONDITIONAL, adr-0014 untouched.
**theories/ElabNs.v** (~1000 lines, 15/15 Print Assumptions closed): elab_ns (one consolidation
layer: 5 store ops escaped + faithful store-backed cache + journal as chronological DList at "j";
wrong-arity cache/journal ops → Ret dstuck_val so ZERO cache/journal ops survive), nsrel (three-armed
find view + empty mid cache/journal), elab_ns_simulates (same skeleton as C1), elab_full = elab ∘
elab_ns + elab_full_simulates (relation-composed) + elab_full_run_top; wf_elab_ns/full; anti-vacuity:
cache put-get + journal 2-append probes through the FULL tower (vm), null-cache + forgetful-journal
mutants rejected, chained-update nsrel_inhabited (nonempty store+cache+journal witness).
Proof-engineering notes (remember): bare cbn near M.find/M.add unfolds M.Raw internals and FMapFacts
rewrites stop matching — use cbn [ns_view] / conversion lemmas (view_u/c/j0 by reflexivity); entry
type ascriptions matter (a pair literal elaborates at dval*option Z ≠ entry and rewrite misses);
`try reflexivity` after repeat split can close vm-computable run-equalities by conversion (count
bullets accordingly).
**Pipeline**: --elab now emits ElabNs.elab_full_programs → progk_generated.ml is the COMPOSED tower
(0 cache/journal/deadline calls — grep-verified); diff_store_k reseeded/observed through the u/c/j
regions; NEW diff_cache_k (3000: cold==warm==reference, CW/CH coverage; NO cache handler in the
stack) + diff_journal_k (300×3×2: outcome+state+trace+decoded-journal, JK1-JK8 incl. throw-prefix
survival and order==input; NO journal handler). Manifest: discharge field on EVERY effect entry
(Store/Cache/Journal derived(<thm>), Time/Error/Env/Trace/Store_kernel kernel-v1) + NEW
ci/check_discharge.sh (field present + derived theorems exist in theories/) wired into ci-checks.
README: tower column in "The effects" + the mode-K/mode-F claim paragraph (adr-0004 wording
discipline). From-clean make all: 19 suites green (3 mode-K), all gates pass.
**TCB bottom line: mode K's trusted effect surface = {Store_kernel, Time, Throw, Ask, Trace} — 5
kernel families; Expiry/Cache/Journal are THEOREMS.** Mode F byte-identical (fused realizers =
performance options; tower-rationale.md holds the why-it-matters arguments).

## Exact next step (post-C2)
Phase C continues per kb/plan-towers.md: **C3** — application 2, a Unix file tool forcing the first
genuinely low-level family (fd byte-stream I/O + process context), ADR-0017 FIRST (family shapes,
error surface, world model for descriptors, realizer contracts), differential vs coreutils.
Also pending from the rationale (user-visible): a redoq mode-K CI leg + measuring the mode-K cost
on redoq's bench at the next pin bump.

## 2026-07-19 — C3 DONE: the file family (ADR-0017) — first low-level kernel family + proven tool
EffIR: +4 ops (OOpen/ORead/OFWrite/OClose), world +3 regions (files/fds/next_fd), handle_file (EOF =
empty chunk; modeled errors ENOENT/EBADF as TAGGED VALUES; malformed = Dstuck). Ripple contained:
mkWorld literal arity (7 files), Journal frame proof (Opaque handle_file + destruct arm), Wf op_arity
+ run_checked twin (soundness proof was shape-generic — zero changes), wrel/nsrel +3 field equalities,
pass tactics gained scrutinee-destruct arms (handle_file/Z.eqb/Z.leb/M.find/fd_find/Z-match/positive-
match); both tower theorems re-verified over the extended world UNCHANGED otherwise.
**theories/FileIO.v** (no Section Variables — the check_no_admitted gate greps assumption vernaculars):
chunking_invariance (concat of chunk_stream = the stream, ANY ml>=1 — buffer size provably
unobservable) + wc_prog_correct (GENERAL: every path/contents/fuel/ml covering the file; loop
invariant threads counter through the store, offset through the fd table; top-down stepping with
run_bind_eq/run_match_eq/run_repeat_eq — do NOT fight cbn normal forms across independently-reduced
fix terms, step with definitional equations instead) + EOF boundary instances + wrong-chunking mutant
(rejected at k*ml±1, plausible at k*ml) + modeled-error instances. Samples: wc_prog fuel/ml family,
sample_wc (8×3), sample_wc_big (64×512 — the 32KiB tool instance, cap STATED), sample_file_rw,
sample_file_missing.
**Runtime**: Rkv.Fileio (Unix.*, no C stubs) — full-read/write loops (EINTR), interposable sys record
(the Time.source pattern), aliasing REFUSED via (st_dev,st_ino) over the open set (cp posture),
size/mtime change DETECTED at close (rsync posture), symlinks followed at open, environmental errors
= Tag(66, reason) at the checked boundary. Manifest: File family + 4 named assumptions
(Runtime_FS_distinct_inodes CHECKED / Runtime_FS_open_inode_stable / Runtime_File{Read,Write}_full).
**tools/rwc**: the C3 app — proven core (sample_wc_big), untrusted wrapper (argv→OAsk ctx, outcome→
exit codes: 0 count, 1 modeled ENOENT, 2 environmental). Handler nesting lesson: Err.run_error must
be INSIDE Fileio.run_checked or the catch-all converts program throws to Unexpected_exception.
**tests/diff_file**: three-way reference == generated == coreutils(`wc -c`) through REAL temp files;
corpora F1-F7 (NUL, high bytes, chunk boundaries k*3±1 and k*512±1, 32KiB, huge line); F8 disk ==
reference file region (write path); F9 modeled-error values; seam checks FI1-FI5 (short-read
interposition, EIO→Environmental, aliasing refusal, symlink follow, change detection). 294 cases, 0
fails, first run. Gallery examples/Files.v; README 16 ops/9 families + File row;
kb/spec/effect-signatures.md file-family section.
Deferred (recorded in plan-towers §C3): PCountByte prim (wc -l), mode-K suites over file samples.

## Exact next step (post-C3)
**C4** per kb/plan-towers.md: sequential HTTP server forcing the sockets family — ADR first (the C3
chunk discipline reused for ORecv/OSend). Then C5 concurrency (constraints pinned in the plan).
Also pending: redoq mode-K CI leg + bench measurement at next pin bump.

## 2026-07-22 — C4 DONE: the socket family (ADR-0018) — a proven HTTP/1.0 server over real TCP
EffIR: +4 ops (OAccept/ORecv/OSend/OCloseConn), world +4 regions (conn_script/socks/conn_log/
next_conn) — determinism by INJECTION: the connection script is the oracle (the C5 recorded-schedule
mechanism rehearsed). Ripple absorbed by the C3 playbook (relations +4 equalities, pass-tactic arms
for handle_sock/sk_find/nil-cons, Journal Opaque). Rider prim PFindSub (17 prims now; manifest +
diff_prims classes incl. first-match overlap + the CRLF request-line case).
**The server**: Samples.http_prog — accept loop; per-connection buffer accumulation (the wc pattern
with bytes); a CONNECTION-FREE parse tree (returns the response value; conn only at send/close —
the de Bruijn discipline that made it writable); route lookup = a collecting Fold over the ctx table.
**theories/SockIO.v**: spec http_response/expected_log; vm smokes FIRST (validated every index before
proving); groundwork (find_sub_bound, bytes_sub_in_range, print_int_in_range); route_fold_correct
(env-generalized against the fold-env-fixation trap); http_parse_correct (spec and program share
scrutinees — destruct in lockstep; cbn exclusion lists keep BOTH sides stable); rc_body_step/rc_loop
(canonical singleton-world shapes, entry-type ascriptions matter); http_handle_correct (folded
stepping: run_bind_eq/run_match_eq/run_repeat_eq + repeat_loop_S — NEVER let cbn unfold run/
repeat_loop; fix-normal-form fights are unwinnable); http_accept_loop; **http_prog_correct** (GENERAL:
every table/script/fuels; ml universally quantified). Anti-vacuity: Content-Length+1 mutant rejected/
plausible; hypothesis inhabitance over the smoke scripts.
**Runtime Rkv.Sockio**: one-shot half-close contract (adr-0018 §1 — the file full-read loop DEADLOCKS
on sockets otherwise; keep-alive deferred to C5); recv/send full loops; SO_RCVTIMEO liveness backstop
(stalled client -> loud Environmental, never a hang); accept on wrapper-closed listener = the
script-exhausted VALUE (the honest live realization of exhaustion); interposable sys.
**tests/diff_sock**: record-and-replay over REAL loopback TCP — forked scripted clients (send,
shutdown-write, read-to-EOF), generated server in the parent; per-connection outputs == reference
transcript; classes S1-S8 + FI1 (short-recv unchanged) + FI2 (timeout backstop) + S7 (pre-closed
listener + empty script = the exhausted path). Harness contract: script length == accept fuel.
**tools/rhttpd**: bind/listen wrapper + the proven core (sample_http_big); smoke-tested with a real
Python HTTP client (200 + body ✓, 404 ✓). Manifest: Socket family + Runtime_Sock_script_faithful /
SockRecv_full / SockSend_full; README 20 ops / 10 families; gallery Sockets.v; spec section.

## Exact next step (post-C4)
**C5** per kb/plan-towers.md: the concurrency effect family — own ADR first (constraints pinned in
the plan: one-shot continuations, schedule-oracle determinism, cooperative fibers + channels,
recorded-schedule replay; the connection-script oracle is the rehearsed mechanism). Also pending:
redoq mode-K CI leg + bench measurement at next pin bump; PCountByte (wc -l); mode-K suites over the
file/socket samples.

## 2026-07-22 — C5 direction set + C5.1 adequacy spike CLOSED
Concurrency capstone: ADR-0019 PROPOSED then open questions RESOLVED via a laconic decision console
(artifact). Resolutions (commit 661ddd4): Q1 IR surface = statically-named tm by index (NO IR change —
the dval-embedding alternative rejected); Q2 channels = OChanMake dynamic creation (spends scope in the
op set, not the adequacy proof — a next_chan counter); Q3 proof scope = spike CEK on Ret/Bind/Perform,
commit if adequacy closes else statement-boundary. Aggregate posture: risk-managed.
**C5.1 SPIKE CLOSED (theories/Cek.v, 4/4 Print Assumptions closed):** the defunctionalized-continuation
step machine (CEK: config = CEval tm env kont world | CRet outcome kont world; one frame KB for Bind;
step reuses run verbatim for Perform so effect-agreement is free) is ADEQUATE to big-step run on the
{Ret,Bind,Perform} fragment. THE theorem cek_run: generalized over an arbitrary continuation k,
star (CEval t env k w) (CRet (fst (run env t w)) k (snd (run env t w))) — proven by PLAIN STRUCTURAL
INDUCTION on tm, no fuel, no measure; the star-relation formulation composes by star_trans. Key moves:
generalize over k (the Bind frame is just a longer k the IH covers); reuse run for Perform; concrete
fuel-driver instance (ex_machine_matches_run, vm_compute) witnesses the reachability is non-vacuous.
**DECISION: commit to the CEK machine** — the frame-stack induction did not fight; Match/Repeat/Prim/Fold
are the scale-up (more frame shapes, same adequacy idea), not new risk. Proof-only file; no codegen/
runtime/test impact; make rocq clean, no-admitted gate green.

## Exact next step (post-C5.1)
Scale cek_run to the FULL tm (add frames for Match branches, Repeat fuel, Fold accumulator, Prim);
prove full-tm adequacy; THEN build the schedule oracle + 5 ops (OSpawn body-by-index / OYield /
OChanMake / OChanSend / OChanRecv) + world regions (fiber pool, channel table, schedule, transcript,
next_chan) + Deadlocked outcome; runtime Effect.Deep scheduler; concurrent HTTP server driver with the
sequential-under-singleton-schedule corollary recovering C4's http_prog_correct. Runtime realizer gets
its own review once full-tm adequacy is in (ADR-0019 status). Also still pending: redoq mode-K CI leg +
bench at next pin bump; PCountByte (wc -l); mode-K over file/socket samples.

## 2026-07-22 — C5 full-tm adequacy CLOSED (theories/Cek.v scaled to the whole term)
Scaled the C5.1 spike from {Ret,Bind,Perform} to the ENTIRE tm. Machine additions: KRep frame
(Repeat — on ORet, REFOCUS as CEval (Repeat m body), so IH(m) applies directly), KFold frame (Fold —
one frame carries remaining elements; the CRet ORet value IS the accumulator, so KFold0/KFoldS unify
to one), select (Match — pure first-match dispatch to a tail-run, NO frame), Prim reuses run verbatim
like Perform (leaf). THE theorem cek_run: adeq t for EVERY t (adeq t := forall env k w, star
(CEval t env k w) (CRet (fst (run env t w)) k (snd (run env t w)))) — strong structural induction
(tm_ind_strong) with the continuation k generalized; three helper inductions close the compound
constructs: cek_match_dispatch (on branch list), cek_repeat (on fuel n), cek_fold (on element list).
cek_adequate = empty-k top level: the machine IS run. Compiled FIRST TRY after the spike; the
prediction held (Match/Repeat/Prim/Fold = frame shapes, not a new idea). 7/7 Print Assumptions closed;
proof-only, no codegen/runtime/test impact; no-admitted gate green. Key moves worth remembering:
generalize over k (a pushed frame is just a longer k the IH covers); reuse run for leaves (agreement
free); refocus KRep as Repeat (not raw body) so the fuel IH lands; unify the two Fold frames via
"CRet value = acc"; definitional step-equations (run_bind/tb_cons/repeat_loop_S/fold_elems_cons) all
by reflexivity. ex_machine_matches_run (vm_compute over a Repeat+Fold+Prim+Perform+Bind term) witnesses
non-vacuity.

## Exact next step (post full-tm adequacy)
Build the concurrency family on the now-validated machine: world regions (fiber pool = list of
(id, config) suspended machines, channel table, schedule : list fiber_id, transcript, next_chan);
the 5 ops (OSpawn body-by-index / OYield / OChanMake / OChanSend / OChanRecv) as machine-level
scheduling steps (a fiber runs via `step` until it blocks/yields/completes, then the scheduler picks
the next per the injected schedule); Deadlocked outcome (all-blocked detection). Determinism theorem
(fixed schedule => deterministic transcript), then the concurrent HTTP driver with the
sequential-under-singleton-schedule corollary recovering C4's http_prog_correct. Runtime Effect.Deep
scheduler gets its own review (ADR-0019 status). Still pending: redoq mode-K CI leg + bench at pin
bump; PCountByte; mode-K over file/socket samples.

## 2026-07-22 — C5 concurrency scheduler built on the CEK machine (theories/Sched.v)
EffIR: +5 conc ops (OSpawn/OYield/OChanMake/OChanSend/OChanRecv), SEQUENTIALLY Dstuck (no world field,
no handle arm — they fall to the handle_store default). Ripple LIGHT (the design paid off): Wf op_arity
+5, Elab/ElabNs perform-sim +5 pass bullets each; NOTHING else (they pass through elab_perform's
default and run's handle_store default). Full tree rebuilds; generated freshness gate green; diff_store
smoke green.
**theories/Sched.v** (5/5 Print Assumptions closed, axiom-free): the cooperative scheduler. Fibers SHARE
one world; a fiber = a world-free CEK frame state (fstate = FE tm env kont | FR outcome kont); fstep
reuses Cek.step (world threaded out via to_cfg/of_cfg). run_to_sched runs a fiber to its next
SCHEDULING POINT (halt or a conc op — fconc detects FE(Perform conc-op)); the scheduler INTERCEPTS the
op (the machine never reduces conc ops). sched_one handles one scheduled fiber; run_sched folds the
injected schedule (a FUNCTION of it — determinism by injection, the C4 script oracle generalized to
interleaving order). Channels = Z-keyed FIFO assoc lists in the scheduler state (NOT the world);
OChanRecv on empty = BLOCK (no progress this slot); deadlock = all fibers blocked → sresult_of = Stuck.
No shared-memory op → data races not representable (structural).
Anti-vacuity (vm_compute, all 5 ops exercised): schedule_matters (fA=trace10;yield;trace11, fB=trace20;
[1;2;1] vs [1;1;2] give DIFFERENT traces — the oracle controls interleaving), interleaving_121 pins
[10;20;11], seq_embedding (a conc-free fiber = its sequential run — trace and outcome), deadlock (mutual
empty-recv → Stuck [1;2] []), producer_consumer (OChanSend 42 / OChanRecv, block-then-progress),
spawn_runs (OSpawn body-by-index adds a fiber that runs). Reaping note: a fiber finishing AT a
conc-op-resume (kont→[]) is reaped only when NEXT scheduled (run_to_sched sees fdone) — schedules end
with a slot to reap such fibers.

## Exact next step (post-scheduler)
GENERAL theorems: (1) run_sched of a SINGLE conc-free fiber under a long-enough singleton schedule =
big-step run (via Cek.cek_adequate + a run_to_sched↔star bridge) — the sequential embedding proven, not
just instanced; (2) determinism stated as a corollary (run_sched is a function). Then the CONCURRENT
HTTP driver: spawn a fiber per accepted connection, recover C4's http_prog_correct under the singleton
schedule. Then (gated on its OWN review per adr-0019) the OCaml Effect.Deep scheduler + differential
(record-and-replay the schedule, the C4 pattern). Still pending: redoq mode-K CI leg + bench; PCountByte;
mode-K over file/socket samples.

## 2026-07-22 — C5 general sequential embedding proven (Cek bridge + Sched embedding)
Two GENERAL theorems (both axiom-free), turning the concrete seq_embedding instance into proven law:
**theories/Cek.v §5b — the executable bridge:** star_drive (any star-reachable HALTED config is reached
by the fuel driver `drive` — via step_halted + drive_stable, halted configs are step-fixpoints so drive
parks) + **cek_drive_run** (GENERAL, every t: exists n, drive n (CEval t env [] w) = CRet (fst (run env
t w)) [] (snd ...)). I.e. the EXECUTABLE step machine computes big-step run for every program — the
statement the OCaml scheduler realizes (running a fiber IS running run). Corollary of cek_adequate +
star_drive.
**theories/Sched.v §5b — the scheduler embedding:** seq_embedding_general (GENERAL): given the clean
machine-interface hypothesis Hrun (run_to_sched RTS_FUEL (FE t [][]) w = (FR (fst run) [], snd run)),
a single-fiber schedule [fid] reaps the fiber into sdone with run's outcome, leaves swld at run's final
world, sfib empty. The scheduler BOOKKEEPING (lookup/reap/done/world) is proven general; Hrun is the
isolated interface to the machine, dischargeable via cek_drive_run (+ conc-free invariant for the fuel-
suffices step, the next unit). fS_runs_to_run discharges Hrun concretely (vm_compute) → seq_embedding_fS
corollary, showing the general theorem is inhabited/usable. Proof note: symbolic fid needs explicit
lookupZ/removeZ helper facts (Z.eqb fid fid = true) — cbn won't reduce Z.eqb on a variable.
Theory-only; no-admitted gate green; 330 closed-assumption lines across theories.

## Exact next step (post general-embedding)
(1) conc-free invariant: conc_free tm + step preserves it + fconc None on conc-free → run_to_sched of a
conc-free fiber = of_cfg ∘ drive, discharging Hrun GENERALLY for every conc-free-and-fuel-sufficient t
(closes the loop: seq_embedding_general holds unconditionally for conc-free fibers). (2) The CONCURRENT
HTTP driver: spawn a fiber per accepted connection; under the singleton (run-to-completion) schedule the
transcript = C4's sequential accept loop, recovering SockIO.http_prog_correct — a real Sched↔SockIO
theorem. (3) Gated on its OWN review (adr-0019): the OCaml Effect.Deep scheduler + record-and-replay
differential (the C4 schedule-as-oracle pattern). Still pending: redoq mode-K CI leg + bench; PCountByte;
mode-K over file/socket samples.

## 2026-07-23 — C5 conc-free invariant + concurrent HTTP driver (Sched↔SockIO closed)
Two-part unit, all axiom-free, theory-only (no codegen/runtime/test churn).
**theories/Sched.v §5c — the conc-free invariant discharges Hrun BY LAW:** `conc_free : tm -> Prop`
(inline nested fix for branch bodies — a genuine mutual fixpoint is rejected by the guard on the hidden
component projection; standalone `conc_free_branches` + `conc_free_Match` bridge). `step_conc_free`
(step preserves conc-freedom: every pushed KB/KRep/KFold frame carries a term the source already
contained, and no conc op is fabricated — `select_conc_free` for the Match arm). `fconc_conc_free` (a
conc-free fiber is never at a scheduling point). Hence **run_to_sched_drive** (run_to_sched of a conc-free
fiber IS `Cek.drive` — via of_cfg/to_cfg roundtrips + fdone↔halted) → **conc_free_embeds** (every conc-free
program embeds into run_to_sched as big-step `run`, existential fuel, from Cek.cek_drive_run) →
**seq_embedding_cf** (the fixed-RTS_FUEL `run_sched` recovers `run` for conc-free programs meeting the
budget; drive_mono + run_to_sched_ge bridge the existential fuel to RTS_FUEL). This turns
seq_embedding_general's Hrun from assumption into theorem for the whole conc-free class.
**theories/SchedHttp.v — the concurrent HTTP driver ↔ the certified server:** (A) `http_driver_seq`
(GENERAL): the proven sequential `http_prog` (conc_free — `conc_free_http_prog`) run as ONE scheduled
fiber recovers `conn_log = expected_log` + `sdone=[(fid,ORet DUnit)]` + `sfib=[]`, via seq_embedding_cf +
SockIO.http_prog_correct (no interpreter re-proof; run_sock = run [] _ sockw definitionally). Smoke
corollary `http_driver_seq_smoke` discharges the fuel budget by vm_compute (hypothesis-free). (B)
`drv_concurrent_matches`: a genuinely CONCURRENT acceptor+worker structure (acceptor OAccepts and
OChanSends each conn on channel 0; worker OChanRecvs and runs the same http_handle arm) produces the
EXACT expected_log under run-to-completion schedule [1;2]×4 — both fibers reaped. `drv_worker_starved`
(schedule [1;1;1;1] → empty transcript) is the schedule-is-load-bearing mutant. Channel handshake note:
channel 0 pre-made in drv_init (snextc=1) and hardcoded VInt 0 in both bodies — sidesteps the
static-body/empty-env vs dynamic-OChanMake tension (a spawned worker can't receive a dynamic channel
handle; the runtime sets up the listener/channel). Print Assumptions: all "Closed under the global
context" (Sched +2, SchedHttp +4). Full `dune build` + no-admitted + stray-perform gates green. 365
Print Assumptions statements across theories.

## Exact next step (post concurrent-driver)
C5 theory is COMPLETE (machine adequate, scheduler exercised on all 5 ops, sequential embedding general
law, conc-free Hrun discharged, concurrent driver recovers the certified transcript). Remaining C5 work,
gated on its OWN review per adr-0019: the **OCaml Effect.Deep scheduler** (near-idiomatic Eio-style,
no Eio dep, one-shot continuations) + **record-and-replay differential** (fast side logs fiber_id at
each scheduling point → reference replays the recorded schedule; adversarial schedules: starvation,
immediate-block, ping-pong, deadlock) + runtime-manifest/TCB entries for the scheduler realizer. Reserved
statement boundary: re-deriving drv_concurrent_matches GENERALLY through the multi-fiber channel plumbing
(§B is concrete-only). Still pending from earlier: redoq mode-K CI leg + bench at next pin bump;
PCountByte (wc -l); mode-K over file/socket samples.
