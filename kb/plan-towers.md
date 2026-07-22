---
id: plan-towers
type: procedure
summary: Phase-C roadmap from the 2026-07-19 design review — implement the effect tower (adr-0016) in two steps (Expiry flagship, then Cache/Journal + the TCB discharge column), then diversify applications to force genuinely low-level effect families (Unix file tool → byte-stream I/O; sequential HTTP server → sockets), capped by the concurrency effect family (user-flagged priority) with its design constraints fixed now.
domain: planning
last-updated: 2026-07-19
depends-on: [adr-0016-effect-towers, plan, prd]
refines: []
related: [adr-0004-trust-model, adr-0014-wf-checker, runtime-manifest, conv-testing-strategy]
---
# Plan — Phase C: effect towers + application diversity

## Provenance and scope
The why lives in the ADRs, not here (register discipline): the 2026-07-19 design review and its
resolutions — including the rejected compiler application and the user-flagged concurrency family —
are recorded in [[adr-0016-effect-towers]] (Context and Corrections); the strategic argument for the
towers is [[tower-rationale]]. This file is the HOW: the phase-C step sequence, scopes, and DoDs.

Each step follows the house pattern: ADR first (where marked), delegated implementation, from-clean
`make all`, trust-diff review, commit, session-state checkpoint. Complete a step fully before the next
(CLAUDE.md workflow).

## C1 — Tower mechanism + Expiry elaboration (flagship) — ✅ DONE 2026-07-19, commit 3f34a1f
Delivered exactly as scoped; theorem `elab_simulates` needed NO wf side condition and NO wp fallback
(the M.Equal relation approach held). `diff_store_k` green first run (3000×5, boundary asserted).
ADR-0016 §2–3: `elab` infrastructure, `elab_expiry`, projection `π`, the refinement theorem
(`observe`-level, for wf programs, every `now`), `wf p -> wf (elab p)`, anti-vacuity mutants (`<`
liveness at the elaborated level), mode-K codegen path (extracted `elab` composed before emission),
`diff_store` in both modes.
- **Why first:** hardest semantics (liveness boundary, lazy expiry through `observe`), highest
  credibility value, zero new realizers — pure proof + plumbing work.
- **Biggest unknown:** proof effort of the simulation with lazy expiry (dead entries physically present
  in the kernel store, absorbed by `π`). If the direct `observe`-equality proof balloons, fall back to a
  keyed-assertion statement via the R14 wp layer (spec/program-logic.md) — decide inside C1, record in
  the ADR.
- **DoD:** theorem axiom-free with mutants + inhabitance; `make all` green with mode-K `diff_store`
  (coverage assertions unchanged); Store manifest entry's expiry aspect flips to `derived(<theorem>)`.

## C2 — Cache + Journal consolidation + discharge column — ✅ DONE 2026-07-19 (same-day as C1)
Delivered per the corrected design: `theories/ElabNs.v` (elab_ns + elab_full, 15/15 Print Assumptions
closed, unconditional); mode K = the composition, one artifact, kernel realizers only;
`diff_cache_k`/`diff_journal_k` green first run; discharge field on every effect entry +
`ci/check_discharge.sh` gate; README tower column + claim wording.

### (original scope, for the record)
The null cache elaboration is unsound (put-then-get distinguishes) and a syntactic namespace check
cannot bound runtime-computed keys — so C2 builds ONE consolidation layer `elab_ns` below Expiry:
store keys escaped `"u"++k`, cache faithfully store-backed at `"c"++k`, journal a chronological DList
at `"j"` — total injective escaping, unconditional theorem, adr-0014 untouched. Mode K becomes the
COMPOSITION `elab_expiry ∘ elab_ns`: one artifact over kernel realizers only (no cache.ml, no
journal.ml). Manifest `discharge` field on every effect entry + CI check that named discharge theorems
exist; README "The effects" gains the kernel/derived column and the adr-0016 §5 claim wording.
- **DoD:** all derived surfaces `derived(<theorem>)`, kernel = {Store_kernel, Time, Throw, Ask, Trace}
  in the TCB report; mode-K runs of the cache/journal suites green over the composed artifact; README
  updated. **This is the pre-redoq-announcement item** — it converts the review's critique into a
  theorem-backed feature before the repo gets outside scrutiny.

## C3 — Application 2: a Unix file tool — ✅ DONE 2026-07-19 (same-day as C1/C2)
Delivered per ADR-0017 (as twice review-refined): the file family (OOpen/ORead/OFWrite/OClose) in
EffIR with pure in-world FS; `FileIO.chunking_invariance` + `wc_prog_correct` (general, axiom-free);
`tools/rwc` (proven core, untrusted wrapper); `diff_file` three-way vs coreutils through REAL files
with the five seam checks (full-read interposition, EIO, aliasing refusal, symlink follow, change
detection); manifest + TCB rows; gallery `Files.v`. Deferred within scope: `PCountByte` prim for
line counts (wc -l); mode-K suites do not yet exercise the file samples.

### (original scope, for the record)
A wc/head/grep-subset utility, chosen because it forces effects nothing current provides:
**byte-stream I/O** over descriptors (`OOpen`/`OReadChunk`/`OWriteChunk`/`OClose`, EOF as a value,
chunked reads so programs handle short reads) plus process context (`OArgv`, `OExit` with code).
- **ADR-0017 first** (family shapes, error surface — ENOENT/EACCES as structured `OThrow` payloads?,
  world model for open descriptors, realizer contracts over `Unix.read`/`write`).
- Differential testing **against coreutils** on generated corpora (adversarial bytes: NUL, no trailing
  newline, huge lines, non-UTF8) + fault injection (short reads, EBADF).
- Deliberately *not* re-founding the kernel Store over file I/O — that is a storage-engine project;
  descent of the level-1 kernel is a separate future ADR per adr-0016 §6.
- **DoD:** the tool proven (spec: e.g. wc counts = reference fold over the byte stream), extracted,
  generated, differentially green vs coreutils; new families in manifest + gallery + README.

## C4 — Application 3: a sequential HTTP server — ✅ DONE 2026-07-22
Delivered per ADR-0018: the socket family (connection-script oracle; one-shot half-close contract —
the file full-read loop deadlocks otherwise, so keep-alive waits for C5); `SockIO.http_prog_correct`
(GENERAL: every table, script, covering fuels; chunk size universally quantified); rider prim
PFindSub; `tools/rhttpd` (proven core serving real HTTP over TCP); `diff_sock` record-and-replay over
real loopback TCP incl. the short-recv seam and the timeout backstop; manifest + TCB + gallery.

### (original scope, for the record)
Forces **sockets**: `OAccept`/`ORecvChunk`/`OSendChunk`/`OCloseConn`. HTTP/1.0 subset (GET, fixed
routes), parsing built from the existing bytes prims (the C3 chunk discipline reused). **Explicitly
sequential** — accept, handle, close, loop via `Repeat`; the reference semantics stays deterministic;
no claim touches concurrency. Differential/golden tests driven by curl + property tests on the
request-line parser (reuse the redoq RESP experience). ADR with the family design first.
- **DoD:** server proven for its route table (response = reference function of the parsed request),
  runs under the generated backend, golden suite green; sockets family in manifest + gallery.

## C5 — Concurrency effects (user-flagged; the capstone)
**Full design: [[adr-0019-concurrency]] (RESOLVED 2026-07-22).** C5.1 spike + full-tm adequacy CLOSED (theories/Cek.v — the CEK step machine equals big-step run over the WHOLE tm, axiom-free); C5 committed to the CEK machine. Scheduler built on the machine (theories/Sched.v): 5 conc ops (sequentially Dstuck, scheduler-intercepted), schedule oracle, channels, deadlock-as-Stuck; anti-vacuity green (schedule_matters/seq_embedding/deadlock/producer_consumer/spawn). Next: general sequential-embedding theorem + concurrent HTTP driver; OCaml runtime gated on review. The constraints below
were fixed at the 2026-07-19 review so C3/C4 built toward them; the ADR turns them into the schedule-oracle
+ step-machine design and names the load-bearing adequacy proof and its fallback. Constraints:
1. **One-shot continuations only** — invariant 7 already forbids multi-shot; the concurrency design must
   never need them.
2. **The reference semantics stays deterministic.** Nondeterminism enters *only* through an explicit
   schedule oracle in `world` (the adr-0011 pattern: inject the source, one instant per run —
   generalized to scheduling decisions). Theorems quantify over schedules; differential tests **replay
   recorded schedules** — the fast side logs its scheduling decisions at yield points, the reference
   replays them (feasible precisely because scheduling is cooperative, so yield points are explicit).
3. **Cooperative fibers + channels**, not shared memory: `OSpawn`/`OYield` + `OChanSend`/`OChanRecv`.
   No data races representable at the IR level; blocking ops (C3/C4 chunk reads, accept) are the yield
   points — which is why C5 sequences *after* them: a scheduler with nothing blocking has nothing to
   schedule.
4. **The backend story is the point:** OCaml 5 effect handlers ARE a fiber runtime — certified
   concurrency compiling to native one-shot-continuation fibers is rocqeteer's strongest differentiator.
   The codegen target should be near-idiomatic Eio-style structure (without taking the Eio dependency —
   budget stays adr-0003 unless an ADR says otherwise).
- **Driver:** upgrade the C4 server to a concurrent accept loop; differential = sequential semantics
  under the singleton schedule, then recorded-schedule replay for concurrent runs.

## Ordering rationale
C1–C2 first: pure proof work, no new realizers, and the announcement-critical credibility fix. C3
before C4: file I/O is the smallest genuinely-low-level TCB increment and its chunk discipline is
reused by sockets. C5 last but constrained now (§C5.1–4), designed alongside C4's server so the
concurrent upgrade is a planned refactor, not a rewrite.

## Non-goals of phase C
No interleaving semantics before C5's ADR; no TLS anywhere (an HTTP *client* was considered and ranked
last for exactly that TCB explosion); no cost/resource proofs (invariant 3); no new opam deps without an
ADR (adr-0003).
