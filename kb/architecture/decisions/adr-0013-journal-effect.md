---
id: adr-0013-journal-effect
type: decision
summary: R9 adds a Journal effect — OJournal appends (now_ms, payload dval) to a world.journal list (newest-first, reversed by observe); rocqeteer proves append/order laws and a generic run-sequence-is-a-fold composition lemma; durability, fsync, and replay-equivalence claims stay consumer-side (the realizer streams to a sink, trusted via the manifest).
domain: architecture
last-updated: 2026-07-11
depends-on: [effir, adr-0011-time-and-expiring-store, adr-0004-trust-model]
refines: []
related: [adr-0010-structured-values, runtime-manifest]
---
# ADR-0013 — The Journal effect (R9)

## Context
Persistence-oriented consumers need an append-only journal: each committed operation appends an entry;
recovery replays the journal to rebuild state (consumer properties: replay equivalence, truncation
tolerance). Requirement R9: "append (tagged entry, timestamp); reference replay = fold". Constraints:
domain-neutrality (no AOF format, no command encoding in the IR), the R4/R5 world model (one `now_ms`
per run, adr-0011), explicit trust (what is PROVEN is the in-memory journal; disk durability is not).

## Decision
1. **World field + one op.** `world.journal : list (Z * dval)`, newest-first (the Trace convention);
   `OJournal [v] -> DUnit` appends `(world.now_ms, eval v)`. The timestamp is the run's single instant —
   entries within one run share it by design (adr-0011: no in-IR clock advancement). `observe_full`
   exposes the journal reversed (chronological), like the trace.
2. **Entries are plain dvals.** A consumer encodes its operations as tagged values (adr-0010 DTag/DList —
   e.g. an entry is its own command representation with absolute deadlines already resolved); rocqeteer
   never sees an entry grammar. No entry validation in the IR (R10 may later type payload shapes).
3. **Replay is composition, and the lemma is generic.** rocqeteer proves, once, over the reference
   semantics: running a LIST of programs in sequence from an initial world equals a left fold of `run`
   over that list (state and journal threading made explicit) — plus the journal laws: append order is
   program order; journal is write-only (no op reads it; a run's outcome is independent of the initial
   journal contents — stated and proven as a frame law). The consumer's replay theorem (rebuild state
   from its encoded entries ≡ original state) composes ITS encoder with this lemma, in ITS repo.
4. **Realizer: buffer + sink.** `runtime/journal.ml`: an Effect.Deep handler appending `(Z.t * Rval.t)`
   to a per-run buffer and invoking an optional sink callback per entry (the consumer's shell decides
   file format, batching, fsync policy). PROVEN claims stop at "the buffer equals the reference journal"
   (differentially tested); everything sink-onward (disk bytes, crash atomicity, fsync) is named consumer
   trust — the manifest entry says so explicitly, and no rocqeteer text may claim journal durability
   (invariant 3's wording discipline).
5. **Effect ordering:** Journal composes like Trace (a state-carrying handler anywhere inside Time's
   scope); no ordering constraint beyond Time-outermost (adr-0011).

## Consequences
- (+) A consumer AOF is: encode command → OJournal it → its replay theorem = its decoder ∘ the generic
  fold lemma. The IR stays format-free.
- (+) The frame law ("outcome independent of prior journal") kills a premortem-style class of accidental
  read-back coupling.
- (−) Shared-instant timestamps mean entry timestamps are per-run, not per-op — consumers needing
  finer resolution must run finer-grained programs (their model already is one command = one run).
- (−) Durability is explicitly NOT proven — repeated in the manifest, the TCB report, and the consumer
  claim rules.

## What this means for implementers
- Anti-vacuity: a sample journaling two tagged entries around a store mutation, proven by vm_compute
  (order + timestamp + payload exact); the frame law with a mutant handler that READS the journal
  (rejected); run-sequence fold lemma exercised by a concrete two-program instance; inhabitance.
- diff suite `diff_journal`: entry order under Repeat/Fold bodies, error short-circuit (entries before
  the throw are kept — matches OErr state-commit semantics), payload shapes across the full dval
  universe, empty runs; sink callback observed equal to buffer.
- vm_compute + existentials: explicit witnesses (theories/Prims.v header note).
