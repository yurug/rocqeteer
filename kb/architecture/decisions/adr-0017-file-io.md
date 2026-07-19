---
id: adr-0017-file-io
type: decision
summary: PROPOSED (C3, user review pending — no realizer lands before approval) — the first genuinely low-level effect family, byte-stream file I/O — 4 kernel ops (OOpen, ORead, OFWrite, OClose) over a pure in-world file system (path→bytes map + descriptor table); EOF is the empty chunk; modeled errors (existence) are tagged VALUES, unmodeled environmental errors abort via OThrow with a tagged payload; process context (argv/env/stdio) reuses OAsk and pre-opened descriptors, adding ZERO ops; realizer over Unix.read/write with a full-read loop contract; differentially tested against coreutils.
domain: architecture
last-updated: 2026-07-19
depends-on: [effir, adr-0004-trust-model, adr-0010-structured-values, adr-0016-effect-towers]
refines: []
related: [plan-towers, adr-0011-time-and-expiring-store, adr-0003-dependency-budget, runtime-manifest]
---
# ADR-0017 — Byte-stream file I/O: the first low-level kernel family (PROPOSED)

> **Status: PROPOSED for C3.** Written ADR-first per the house pattern; this is the design the
> 2026-07-19 review asked to see *before* syscall-level realizers enter the TCB. Nothing below is
> implemented; approval gates C3.

## Context
Phase C3 ([[plan-towers]]) diversifies applications with a Unix file tool (wc/head-subset) chosen to
force effects nothing current provides: reading and writing **byte streams over descriptors**, plus
process context. Constraints: the reference semantics stays a **pure deterministic function** (the
proof target and test oracle); one EffIR (invariant 1); the dependency budget (adr-0003 — `unix`
ships with the compiler and is already declared for the Time wall clock); domain-neutrality (no
tool-specific ops); explicit trust (every realizer contract in the manifest, adr-0004). This family
is **kernel-v1** in tower terms (adr-0016 §6): it bottoms out in syscalls and is irreducible at this
level — while opening the *future* option of deriving today's Store kernel over it (out of scope).

## Decision
1. **Four ops, one new world region.** `world` gains `files : M.t (list ascii)` (path → contents;
   the same string-keyed map as the store), `fds : M.t fd_entry` with
   `fd_entry = (path, offset, mode)` keyed by decimal fd, and `next_fd : Z`. Ops (all results in the
   existing dval universe; adr-0010 tags for sums):
   - `OOpen [path; mode]` — mode `DInt 0` = read (path must exist), `DInt 1` = write-truncate
     (creates/empties). Returns `DTag 0 (DInt fd)` on success, `DTag 1 (DInt code)` on the ONE
     modeled failure: open-for-read of an absent path (`code` = 2, the errno-ENOENT convention).
     Append/read-write modes are deferred (YAGNI until an app forces them).
   - `ORead [fd; maxlen]` — returns `DBytes chunk` with
     `chunk = contents[offset .. offset + min(maxlen, remaining))`, advancing the offset.
     **EOF is the empty chunk** (`maxlen >= 1` is the caller's obligation; `maxlen <= 0` is Dstuck).
     No option, no sentinel — deterministic, and the chunk discipline forces programs to handle
     partial data, which C4's sockets will reuse.
   - `OFWrite [fd; bytes]` — appends at the descriptor's offset (write-mode fds only), returns
     `DUnit`. Short writes DO NOT EXIST at the IR level (see Decision 3).
   - `OClose [fd]` — removes the descriptor, `DBool` (was it open). Double-close is `DBool false`,
     not an error — matching ODelete's shape.
   Malformed arguments (non-int fd, non-bytes path, unknown mode) are `Dstuck`, the existing
   convention. Ops on closed/unknown fds: `DTag 1 (DInt 9)` (EBADF convention) — a VALUE, since
   programs legitimately probe descriptors.
2. **Process context adds ZERO ops.** argv and environment ride the existing Reader: the shell
   wrapper packs them into the `OAsk` context (a consumer convention, like redoq's command
   encoding — rocqeteer never sees an argv grammar). stdin/stdout are PRE-OPENED descriptors 0/1
   seeded in the initial world (stdin = a `files` entry read via fd 0; stdout = a write fd whose
   final contents ARE part of the observable). Exit codes are the shell wrapper's mapping of the
   final outcome (`ORet`/`OErr` + a consumer-tagged payload) — no `OExit` op; the Error effect
   already provides abort.
3. **The modeled/unmodeled error line is explicit.** The reference models exactly ONE failure cause:
   existence (ENOENT on read-open; EBADF on stale fds). Everything environmental — EACCES, EIO,
   ENOSPC, signals — is OUTSIDE the model: the realizer maps such errors to an `OThrow`-style abort
   with payload `DTag 66 (DBytes errno-name)` at the checked boundary (fail-loud, typed; 66 = the
   reserved environmental-failure tag, in the manifest). Consequently: **the correctness theorems
   quantify over runs where the environment cooperates**; environmental aborts are trusted plumbing,
   exercised by fault injection, never silently absorbed. This is invariant-3 wording discipline
   applied to I/O: we prove the data path, we TEST the failure path.
4. **Realizer contract (runtime/fileio.ml, no C stubs).** `Unix.openfile/read/write/close` behind
   an `Effect.Deep` handler; `ORead` LOOPS on short reads until `min(maxlen, remaining)` bytes or
   EOF; `OFWrite` loops until fully written. The loop contracts are what make Decision 1's
   deterministic chunks realizable — they are named manifest entries (`Runtime_FileRead_full`,
   `Runtime_FileWrite_full`), validated by fault injection (interposed short-read sources in tests).
   Buffered vs direct is unobservable; the realizer uses plain `Bytes` buffers.
5. **Observable and testing.** `observe` gains the final `files` map (sorted, like the store) and
   per-fd offsets are NOT observable (closing normalizes). The differential suite runs the C3 tool
   against **coreutils** on generated corpora (NUL bytes, no trailing newline, huge lines, non-UTF8,
   empty files) plus fault injection (absent files, stale fds, short-read interposition). Corpus
   entries persist per invariant 5.
6. **Sizing guard.** v1 fragment = exactly these 4 ops + 2 modes. No seek, no stat, no directories,
   no append, no pipes: each waits for an application that forces it (the adr-0006 discipline that
   kept the store honest).

## Consequences
- (+) The first family whose ops *cannot* be suspected of being application-sugar — the tower's
  kernel grows downward, as the 2026-07-19 review asked.
- (+) The chunk discipline (empty-chunk EOF, caller-driven sizes) is exactly what C4 sockets reuse.
- (+) Zero new ops for process context; zero new deps.
- (−) The environment-cooperates qualifier is a REAL weakening vs the store's total model — stated
  in the manifest and in every consumer claim (Decision 3's wording is mandatory).
- (−) The full-read/full-write loop contracts are new trusted code paths; they get dedicated fault
  tests, not just happy-path differentials.
- (−) A single-process model: concurrent external mutation of the same files is out of scope until
  C5 (documented, not defended).

## What this means for implementers (post-approval)
- Anti-vacuity: a proven wc-core theorem (counts = a fold over the byte stream) with a
  wrong-chunking mutant; inhabitance on a multi-chunk file; EOF-at-boundary instances (file size =
  k·maxlen ± 1).
- The wf checker gains the two op arities only; no typing changes.
- New world fields follow the R4 pattern (fields + `set_` helpers; every existing proof untouched
  by construction — verify with the full suite before any new theorem).
- Realizer manifest entries BEFORE code review, per adr-0004.
