---
id: adr-0019-concurrency
type: decision
summary: PROPOSED (C5 capstone, user review pending — no realizer lands before approval) — cooperative concurrency via a SCHEDULE ORACLE (the C4 connection-script pattern generalized from content to interleaving); the hard part is representing a suspended fiber first-order — resolved by a defunctionalized continuation (a frame-stack STEP MACHINE over the SAME tm, not a second IR), load-bearing obligation = prove the machine agrees with big-step run on the concurrency-free fragment so the oracle is preserved; 4-5 ops (OSpawn/OYield/OChanSend/OChanRecv, maybe OChanMake), channels the only sharing (no shared memory, no data races representable), one-shot continuations (invariant 7); deterministic given the schedule, theorems quantify over schedules, differential replays recorded schedules; backend = OCaml 5 Effect.Deep fibers (Eio-style, no Eio dep); driver = the C4 server's accept loop made concurrent, sequential semantics recovered under the singleton schedule.
domain: architecture
last-updated: 2026-07-22
depends-on: [effir, adr-0001-first-order-ast, adr-0004-trust-model, adr-0011-time-and-expiring-store, adr-0016-effect-towers, adr-0018-sockets]
refines: []
related: [plan-towers, tower-rationale, runtime-manifest]
---
# ADR-0019 — Cooperative concurrency: the schedule oracle and the fiber step machine (PROPOSED)

> **Status: PROPOSED for C5 (the phase-C capstone).** ADR-first per the house pattern; syscall/runtime
> realizers await approval. This ADR leads with the representation problem (§Context) because it is the
> make-or-break decision, and names its biggest proof risk with a scoped fallback (§Decision 2, §Risk).

## Context — the representation problem, stated first
C5 ([[plan-towers]] §C5) is the user-flagged missing family: concurrency. Every prior family threaded
one `world` through a big-step `run env t w : outcome * world` that runs `t` **to completion**. That is
exactly what concurrency cannot do: interleaving means fiber A runs until it yields or blocks, fiber B
runs, then **A resumes where it left off**. A suspended fiber is a *resumption* — a continuation — and
`run` has no notion of one. This is the crux, and it is genuinely harder than C3/C4 (which added world
regions but left `run`'s shape untouched).

The pinned constraints ([[plan-towers]] §C5, fixed at the 2026-07-19 review so C3/C4 built toward them):
one-shot continuations only (invariant 7 already forbids multi-shot); the reference stays deterministic
with nondeterminism entering **only** through a schedule oracle in `world`; cooperative fibers + channels
(no shared memory); the backend is OCaml 5 effect handlers (a fiber runtime already). The oracle is not a
new idea — it is the C4 **connection-script pattern** ([[adr-0018-sockets]]) generalized from *arrival
content* to *interleaving order*; C4 deliberately rehearsed it. Hard constraint: invariant 1 — one EffIR,
two backends; concurrency must not introduce a second *program* representation.

## Decision
1. **The schedule oracle (determinism by injection, the adr-0011/0018 pattern).** `world` gains a
   **fiber pool** (id → fiber state), a **channel table** (id → FIFO queue of dvals + blocked-sender/
   receiver lists), a **schedule** (a `list fiber_id` consumed like fuel — the run order chosen at each
   scheduling point), and the **completed-fiber transcript** (the observable). Nondeterminism lives
   ONLY in the schedule: a **fixed schedule ⇒ a deterministic transcript** (the theorem). The reference
   quantifies over schedules; the differential harness RECORDS the fast scheduler's decisions at yield/
   block points and REPLAYS them as the reference schedule (feasible precisely because scheduling is
   cooperative — yield points are explicit, finite, and logged).
2. **The mechanism: a defunctionalized continuation — a STEP MACHINE over the SAME `tm`, not a second
   IR.** A suspended fiber is represented first-order as `(tm, kont)` where `kont` is a **frame stack**
   — a `list frame` with `frame ::= KBind tm | KMatch ... | KFold ...` (one frame per `run` recursion
   that has an unfinished continuation). A `step : machine -> machine_result` performs ONE reduction of
   the focused `tm`, pushing/popping frames; on a concurrency op (`OYield`, `OChanRecv` on empty,
   `OChanSend` on full) it returns **Blocked (reason, tm, kont)** — the resumable fiber, first-order.
   This is a CEK/CESK-style machine: the **control** is `tm`, the **continuation** is the defunctionalized
   frame stack. **Programs are still `tm`** — the frame stack is an *evaluation mechanism*, not a program
   the user writes or the codegen mirrors. Invariant 1 holds: one EffIR; the machine is a second
   *evaluation strategy*, the standard move (CompCert's compiler passes, CakeML's CEK), not a second AST.
3. **THE LOAD-BEARING OBLIGATION: the machine preserves the big-step oracle.** A second evaluation
   strategy is only honest if it *agrees* with the proven one. So: **prove `run_machine` (the step
   machine driven to completion on a single fiber with no concurrency op) equals `run`** on outcome and
   world, for every program. This is `run`-vs-machine adequacy — the theorem that keeps C5 from becoming
   an unvalidated second semantics. Every C0–C4 theorem then transfers: the sequential fragment's oracle
   is unchanged, and concurrency is a *conservative extension* (a program with no `OSpawn` runs
   identically to today). Anti-vacuity is built in: if adequacy fails, the whole family is rejected.
4. **Four ops (maybe five), channels the only sharing.** `OSpawn [body]` (body a `tm` value — a
   *thunk*; adr-0010 already crosses first-order code as data? NO — see §Open) enqueues a new fiber,
   returns its id; `OYield []` → the scheduler; `OChanSend [ch; v]` / `OChanRecv [ch]` block-and-resume
   via the channel table; optionally `OChanMake []` → a fresh channel id (or channels are pre-created in
   the initial world, like C4's stdio fds — decide in review). **No shared mutable memory op** — fibers
   share ONLY through channels, so **data races are not representable** (the strongest safety property in
   the project, structural not proven). One-shot continuations throughout (invariant 7): a resumed
   `(tm, kont)` is consumed, never re-run.
5. **Deadlock is a modeled OUTCOME, not a hang.** A schedule that leaves every live fiber blocked is a
   *stuck* transcript — the reference detects "all fibers blocked, none runnable" and ends with a
   `Deadlocked` outcome (like `OErr`, an explicit result). The realizer needs a matching detector or it
   would hang; that detector is a **named liveness contract** (the C4 recv-timeout lesson): a runtime
   that cannot make progress aborts loudly, never silently hangs.
6. **Backend: OCaml 5 effect handlers ARE the fiber runtime — the differentiator.** Codegen targets a
   small `Effect.Deep`-based cooperative scheduler (a ready queue + per-channel wait queues), Eio-shaped
   but WITHOUT the Eio dependency (budget adr-0003 unchanged unless a later ADR says otherwise).
   `OYield`/channel ops become `Effect.perform`; the deep handler is the scheduler; one-shot `continue`
   matches the one-shot-continuation invariant exactly. Certified cooperative concurrency compiling to
   native OCaml 5 fibers is rocqeteer's strongest single claim — the reason C5 is the capstone.
7. **Driver: the C4 server, concurrent.** Upgrade `sample_http`'s accept loop to spawn a fiber per
   connection ([[adr-0018-sockets]]). The **sequential semantics is a proven corollary**: under the
   singleton schedule (always run the current fiber to block), the concurrent server's transcript equals
   the C4 sequential server's — so C4's `http_prog_correct` is recovered, not rewritten. Concurrent runs
   are validated by recorded-schedule replay.
8. **Kernel-v1 in tower terms.** The scheduler realizer is syscall-adjacent (Effect.Deep) and irreducible
   at this level (adr-0016 §6); its discharge entry is `kernel-v1`. The schedule oracle is a
   `tcb-assumption` validated by replay, exactly like `Runtime_Sock_script_faithful`.

## Consequences
- (+) The strongest safety property in the project comes for free: no shared memory ⇒ no data races,
  structurally. And the strongest capability claim: certified concurrency on native OCaml 5 fibers.
- (+) The schedule oracle reuses the C4-proven record-and-replay mechanism; determinism is preserved the
  same way time and arrival-content were.
- (+) Conservative extension: every existing theorem survives via the adequacy theorem (§Decision 3);
  redoq and the C0–C4 apps are untouched.
- (−) **The adequacy proof (§Decision 3) is the biggest single proof risk in the project** — a CEK
  machine agreeing with a big-step interpreter over the WHOLE `tm` (Bind/Match/Repeat/Fold nesting) is a
  real induction with a frame-stack invariant. See §Risk for the scoped fallback.
- (−) `run` gains a genuinely new shape (the step machine) — unlike C3/C4, this is not "add a world
  field." The big-step `run` stays as the oracle; the machine is added beside it and proven equal.
- (−) A new liveness contract (the deadlock detector) enters the trusted runtime surface.
- (−) Fairness/starvation are NOT modeled (a schedule may starve a fiber); stated, not defended — the
  schedule is adversarial input, and the theorems hold per-schedule.

## Risk and the scoped fallback (decide in review)
If the full CEK-vs-`run` adequacy proof over the entire `tm` balloons, the fallback is **structured
concurrency with block-at-statement-boundaries only**: fibers suspend ONLY at a top-level `Bind`/`OYield`
boundary, never mid-expression, so a suspended fiber is a *whole `tm`* (the residual continuation is
literally the tail `tm`), no frame stack, no CEK machine — `run_until_block` reuses `run` on each segment.
Weaker (a fiber cannot block inside a `Match` scrutinee's sub-computation), but real cooperative
concurrency, and its adequacy is near-trivial (each segment IS a `run`). Recommendation: **attempt the
CEK machine; fall back to statement-boundary blocking if the adequacy induction does not close in the
C5.1 spike.** This is the C1 pattern (attempt the strong theorem, named fallback ready) at higher stakes.

## Open questions for review (gate implementation)
- **`OSpawn`'s body as data.** A spawned fiber's body is a `tm`. Does it cross the op boundary as a
  first-order `tm` value (needs a `dval` embedding of `tm` — a real IR extension, invariant-1-adjacent),
  or is the fiber body a *statically named* closed `tm` the program references by index (no IR change,
  the redoq/argv pattern)? The latter is strongly preferred; confirm it suffices for the concurrent
  server (one fiber body: handle-connection).
- **Channels: pre-created vs `OChanMake`.** Dynamic channel creation is more expressive but adds an op
  and an id-allocation story; the server needs only per-connection channels. Pre-create in the initial
  world (C4 stdio pattern) unless review wants dynamism.
- **CEK vs statement-boundary** (§Risk) — the load-bearing scope decision.

## What this means for implementers (post-approval)
- **C5.1 spike FIRST**: build the step machine, prove adequacy on a 3-construct fragment
  (Ret/Bind/Perform); if it closes, scale to the full `tm`; if it fights, take the statement-boundary
  fallback. Do not build ops/realizer/app until adequacy is proven on the real fragment.
- Anti-vacuity: a two-fiber ping-pong whose transcript DIFFERS under two schedules (determinism is
  per-schedule, not absolute — the mutant is a scheduler that ignores the oracle); a deadlock instance
  (two fibers each blocked on the other's channel) reaching `Deadlocked`; the sequential-corollary
  instance (singleton schedule = C4 transcript).
- Differential: the fast scheduler logs (fiber_id at each scheduling point) → the reference schedule;
  compare transcripts. Adversarial schedules: starvation, immediate-block, ping-pong, deadlock.
- Realizer manifest entries BEFORE code review (adr-0004); the deadlock detector is a named liveness
  contract; the schedule-faithful assumption is replay-validated.
- Wf checker gains the op arities only; no typing changes (the fiber-body-by-index decision keeps `tm`
  unchanged).
