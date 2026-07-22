---
id: adr-0018-sockets
type: decision
summary: PROPOSED (C4, user review pending — no realizer lands before approval) — the sockets family for the sequential HTTP server — 4 kernel ops (OAccept, ORecv, OSend, OCloseConn) over an injected CONNECTION SCRIPT (the adr-0011 oracle pattern generalized; the C5 recorded-schedule idea in miniature); v1 connections are ONE-SHOT and half-close driven because the file family's full-read loop DEADLOCKS on sockets otherwise; modeled errors (script exhausted, bad conn) are values; TCP's per-connection ordered-reliable contract is the named seam; listener setup is wrapper-owned (zero setup ops); one rider prim PFindSub for delimiter parsing.
domain: architecture
last-updated: 2026-07-22
depends-on: [effir, adr-0004-trust-model, adr-0011-time-and-expiring-store, adr-0016-effect-towers, adr-0017-file-io]
refines: []
related: [plan-towers, adr-0009-vprim-registry, runtime-manifest]
---
# ADR-0018 — Sockets: the connection-script family for the sequential server (PROPOSED)

> **Status: PROPOSED for C4.** ADR-first per the house pattern; syscall-level realizers await
> approval, as with adr-0017. The reasoning-model and seam analysis are in the body up front this
> time — the recv-loop question below is the one that shaped everything.

## Context
C4 ([[plan-towers]]) is the sequential HTTP server, forcing effects nothing current provides:
accepting connections and exchanging byte streams over them. Constraints: the reference semantics
stays a pure deterministic function; sequential only (accept–handle–close, one connection at a time —
concurrency is C5); the C3 chunk discipline reused where it survives; dependency budget unchanged
(`unix` only); domain-neutral ops (no HTTP in the IR); explicit trust. This family is **kernel-v1**
(syscall-backed, adr-0016 §6).

**The modeling decision that everything follows from:** a server's input is inherently
nondeterministic (who connects, what they send, when). Determinism is restored the same way adr-0011
restored it for time — by INJECTION: the world carries a **connection script**, an ordered list of
per-connection input byte streams, and the ops consume it. The theorems quantify over scripts; the
differential harness RECORDS what live clients actually sent and REPLAYS it as the reference's
script. This is exactly the C5 recorded-schedule pattern in miniature — C4 deliberately rehearses
the mechanism on the simplest nondeterminism (arrival content) before C5 applies it to interleaving.

**The seam analysis that constrains the design (the adr-0017 §Reasoning-model question, asked
first this time):** the file family's full-read loop does NOT transfer to sockets. `ORead`'s
deterministic chunk (`min(maxlen, remaining)`) is realizable for files because the realizer can loop
until `maxlen` or EOF — EOF is always eventually there. On a socket, "remaining" is not knowable:
a realizer looping to fill `maxlen` while the client waits for a response before sending more is a
DEADLOCK, and returning "whatever is available" is nondeterministic (racing the client's writes).
The deterministic options are: (a) length/delimiter-driven reads (parser decides how much to ask
for — but the amount available is still racy), or (b) **EOF-driven one-shot connections**: the
client sends its entire request and HALF-CLOSES (shutdown-write); the server reads to EOF, responds,
closes. Under (b) the file discipline transfers verbatim — the recv loop terminates on the
half-close EOF, chunks are deterministic, no deadlock. So:

## Decision
1. **v1 connections are ONE-SHOT and half-close driven.** The protocol contract (stated in every
   consumer claim): a client sends its full request, half-closes, reads the response to EOF. This is
   HTTP/1.0-without-keep-alive semantics. Keep-alive and pipelining are EXPLICITLY deferred to C5 —
   they require "bytes available now" semantics, which is precisely the nondeterminism the C5
   schedule oracle exists for. No silent capability gap: the restriction is the data-plane
   counterpart of "sequential".
2. **Four ops, script-driven.** `world` gains the pending script `conn_script : list (list ascii)`
   (one entry per future connection: that client's complete input), an open-connection table (conn
   id → input, read offset, accumulated output — the fd-table pattern), and a per-run transcript of
   finished connections (the observable). Ops:
   - `OAccept []` — pops the next scripted connection: `DTag 0 (DInt conn)`; script exhausted is the
     VALUE `DTag 1 (DInt 11)` (the EAGAIN convention), which is how a `Repeat`-bounded accept loop
     terminates deterministically. (Live, accept blocks; a bounded run covers the connections that
     arrived — the refinement statement is over completed accepts.)
   - `ORecv [conn; maxlen]` — `DBytes chunk` exactly as [ORead]: `min(maxlen, remaining-in-script)`,
     EMPTY = the client's half-close; `DTag 1 (DInt 9)` on a bad conn id. Same `file_chunk`, same
     boundary lemmas, same chunking-invariance reuse.
   - `OSend [conn; bytes]` — appends to the connection's output; `DUnit` | `DTag 1 (DInt 9)`.
   - `OCloseConn [conn]` — finalizes the connection into the transcript; `DBool` (double-close
     false, the ODelete/OClose shape).
   Malformed args are `Dstuck`. The OBSERVABLE is the ordered transcript: per connection, (input
   script, output bytes) — response correctness is stated against it.
3. **Listener setup is wrapper-owned — zero setup ops.** bind/listen/port, like argv and stdio in
   adr-0017 §2, belong to the untrusted shell: the realizer's `run` takes an already-listening
   socket. The IR stays domain- and deployment-neutral.
4. **Modeled vs environmental, the adr-0017 line.** Modeled as VALUES: script exhaustion (EAGAIN
   convention) and bad conn ids (EBADF convention). Environmental — ECONNRESET mid-recv, EPIPE on
   send, EMFILE, listener errors — aborts the RUN with the tagged `Tag(66, reason)` at the checked
   boundary. A reset mid-conversation is thus OUTSIDE the v1 theorems (fault-injection tested, never
   silent); per-connection degradation (reset as a modeled value) is a recorded possible refinement
   once an application actually wants to handle it.
5. **Realizer (runtime/sockio.ml, no C stubs) + named seam.** `Unix.accept/recv/send/close` behind a
   deep handler with the interposable `sys` record (the fileio pattern; fault injection injects
   resets/short ops):
   - `Runtime_Sock_script_faithful` — the recorded-oracle refinement: the reference script IS what
     the clients sent — per connection, TCP's own contract (ordered, reliable, complete-to-EOF byte
     stream) carries the within-connection half; accept order defines the across-connection order.
     Validated by record-and-replay in the differential suite, not assumed blindly.
   - `Runtime_SockRecv_full` — the recv loop reads until `maxlen` or EOF; terminates BECAUSE of
     Decision 1 (half-close guaranteed by the protocol contract). EINTR discharged in the loop.
   - `Runtime_SockSend_full` — the send loop writes all bytes (EINTR/partial sends discharged).
   - One-shot lifecycle enforced by the realizer: recv-after-response is not in the op flow the
     server core generates; the harness's clients half-close by construction.
6. **The application: `rhttpd`, HTTP/1.0 GET subset — HTTP lives in the PROGRAM, not the IR.** The
   route table is the injected Reader context (a `DList` of (path, body) pairs — adr-0010 values);
   the server core is domain-neutral "respond per the injected table". Request parsing (request
   line, method, path) is built from bytes prims; this needs ONE rider prim (adr-0009 ADR-free
   discipline, manifest + diff tests mandatory): `PFindSub [hay; needle] -> DSome (DInt index) |
   DNone` — first-occurrence substring search, totally shape-checked. With `PFindSub` + `PBytesSub`
   + `PEqBytes`, "GET /p HTTP/1.0\r\n..." parsing is expressible; responses are `PPrintInt`
   (Content-Length) + `PBytesConcat`. THE THEOREM (C4's `wc_prog_correct` analog): for every route
   table, every connection script, and fuel covering it — each connection's output equals the
   reference response function of its request bytes (200+body on a route hit, 404 on a miss, 400 on
   a malformed request line), with the boundary instances at chunk-split request lines (the request
   delimiter falling ON a chunk boundary is the mutant-killing corner).
7. **Testing.** The differential harness drives REAL loopback connections with its own scripted,
   half-closing clients (we control both ends; the protocol contract of Decision 1 is enforced by
   construction), records what was sent, replays it as the reference script, and compares
   transcripts three-ways where possible (reference == live server == recorded outputs). Adversarial
   corpora: chunk-boundary-split request lines, NUL/high bytes in paths, oversized requests, empty
   input, missing half-close (fault case → the recv loop's timeout guard aborts environmentally —
   loud, not hung: the realizer arms a receive timeout as its liveness backstop, manifest-noted).
   curl smoke tests ride along where its lifecycle is compatible; the harness clients are the
   oracle, since curl does not half-close after sending.
8. **Sizing guard.** Four ops, one rider prim. No keep-alive, no pipelining (C5), no concurrent
   connections (C5), no TLS (plan non-goal), no UDP, no client-side connect op (an HTTP client
   ranked last in plan-towers for TCB reasons; `OConnect` waits for an app that forces it).

## Consequences
- (+) The C3 chunk discipline and its lemmas transfer verbatim under the one-shot contract; the
  chunking-invariance principle gets its second, independent consumer.
- (+) The connection-script oracle rehearses C5's recorded-schedule mechanism on simple
  nondeterminism — C5 becomes an extension of a proven pattern, not a new idea.
- (+) HTTP stays consumer-side (the redoq RESP lesson): the IR gains a transport, not a protocol.
- (−) The one-shot restriction is REAL: no keep-alive until C5. Stated in the ADR, the manifest, and
  every consumer claim — the honest counterpart of "sequential".
- (−) A new liveness backstop enters the trusted surface (the recv timeout that converts a
  never-half-closing client into a loud environmental abort instead of a hang) — a realizer
  contract with fault tests, like the full-read loops.
- (−) Mid-connection resets abort the run in v1; graceful per-connection degradation is deferred.

## What this means for implementers (post-approval)
- Anti-vacuity: the server theorem ships with a request-line-split-across-chunks boundary instance,
  a mutant response function (wrong Content-Length) rejected observably, a mutant parser (delimiter
  off-by-one) rejected at the chunk boundary, and inhabitance on a multi-connection script.
- `PFindSub`: reference definition + realizer + manifest row + diff_prims classes (needle at
  boundaries, empty needle, needle == hay, overlapping candidates) before the server uses it.
- World regions follow the R4 field pattern; wrel/nsrel gain the new-field equalities exactly as C3
  did; the pass tactics' scrutinee arms are expected to absorb the new ops without new machinery.
- Realizer manifest entries BEFORE code review (adr-0004); the sys record is the fault seam.
