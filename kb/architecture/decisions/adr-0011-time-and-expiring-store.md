---
id: adr-0011-time-and-expiring-store
type: decision
summary: R4+R5 in one design — world gains an immutable-per-run now_ms read by a new Time effect (ONow), and the Z-keyed KV is REPLACED by a bytes-keyed store with per-binding optional deadlines (live iff now_ms <= deadline; expired = semantically absent everywhere); TTL policy/rounding stays consumer-side, realizers share one injectable time source.
domain: architecture
last-updated: 2026-07-11
depends-on: [effir, adr-0001-first-order-ast, adr-0009-vprim-registry, adr-0004-trust-model]
refines: [adr-0001-first-order-ast]
related: [adr-0008-general-match, adr-0010-structured-values, runtime-manifest]
---
# ADR-0011 — Time and the expiring store (R4 + R5)

## Context
Downstream engines need keys that expire (R4: bytes-keyed store with per-key deadline metadata) and a way
to read the clock (R5: `now_ms`, with an OCaml realizer whose source is injectable so tests share the
oracle's virtual clock). The two are one design: the store's read semantics consult the clock. Constraints:
one IR (invariant 1 — no second store beside the Z-keyed KV), domain-neutrality (no TTL rounding or
SET-command policy in the IR), totality of `run`, explicit trust (ADR-0004), depth-1 Match / prim
discipline unchanged.

## Decision
1. **Time (R5): `world.now_ms : Z`, immutable within a run.** A new effect `Time` with one op
   `ONow : [] -> DInt now_ms`. There is NO in-IR clock-advancing op in v1: a program executes atomically
   at one instant (the consumer's single-command model; its harness advances the clock BETWEEN runs —
   the same protocol its oracle uses). `run_top` gains a `now` parameter alongside `ctx`.
2. **Store (R4): the Z-keyed KV is REPLACED** (no legacy twin — same posture as adr-0008's MatchOpt
   removal). `world.kv : map from byte-string keys to (dval * option Z)` — value plus optional absolute
   deadline in ms. Ops (args are `val`s; keys are `VBytes`):
   ```
   OGet         [k]     -> DNone | DSome v                       (live bindings only)
   OPut         [k; v]  -> DUnit    stores v and CLEARS any deadline
   ODelete      [k]     -> DBool    true iff a LIVE binding was removed
   OGetDeadline [k]     -> DNone (no live k) | DSome DNone (live, no deadline)
                           | DSome (DSome (DInt d))
   OSetDeadline [k; VNone | VSome (VInt d)] -> DBool  true iff a live binding was modified
   ```
   Composition covers the consumer surface without policy leaking in: SET-with-TTL =
   `Bind (OPut k v) (OSetDeadline k (Some d))` (atomic — the IR has no interleaving); KEEPTTL =
   read the deadline first, restore it after the put. TTL *rounding*, negative-expire-deletes, and reply
   codes are consumer programs built from prims — NOT IR semantics.
3. **Liveness is the ONE rule** (oracle-observed, boundary-critical): a binding `(v, Some d)` is live iff
   `now_ms <= d` — alive AT the deadline, dead strictly after. `(v, None)` is always live. Every op and
   `observe` see expired bindings as ABSENT (observe filters by the run's `now_ms`); whether a realizer
   physically deletes them is unobservable implementation freedom (lazy deletion allowed).
   Provenance: single-probe observed (verdis O1, 2026-07-10); the 10k-case prediction-vs-oracle run
   validates it at scale before this ADR's implementation merges — if that run contradicts the boundary,
   THIS section changes first.
4. **One time source, injected.** `runtime/time.ml`: a handler whose source is a closure
   (`unit -> Z`, milliseconds); production wall clock by default, tests inject the harness-controlled
   virtual clock (the SAME file the consumer's oracle reads via libfaketime). The store realizer
   (`runtime/kv.ml`, generalized) obtains `now` from the SAME source instance — the runtime exposes one
   composition point that constructs both handlers from one source, and the manifest records
   "store-now ≡ time-now, single source" as a named assumption. Within one program run the fast side
   reads the source per-op while the reference used one `now_ms` — the injected TEST source is stepped
   only between runs, so both sides see one instant per run; the production source is monotonic wall
   clock, and cross-op drift within a run is outside the refinement statement (documented, not proven).
5. **Migration**: all Z-keyed samples/proofs/diff suites move to byte-string keys (decimal-bytes of the
   old integer keys where meaning is preserved); `incr_correct` and the KV laws are re-proven over the
   generalized store (deadline-less ops behave exactly as before); codegen's `emit_key` becomes a bytes
   emitter; `Kv.get/put/delete` runtime signatures change to `bytes` keys and gain deadline variants.
   Diff suites gain `diff_store` (deadline boundaries d-1/d/d+1, key collisions, put-clears-deadline,
   setdeadline-on-missing) and `diff_time` (now flows to programs; 0/negative/2^62 boundary values).

## Consequences
- (+) The consumer's EXPIRE/TTL/PERSIST/SET-EX surface is expressible today; its exact reply-code and
  rounding quirks stay in ITS programs (domain-neutrality preserved).
- (+) The determinism protocol (virtual clock + between-run stepping + lazy expiry) is now a first-class
  runtime concept shared by reference and fast sides — differential tests of time-dependent behavior are
  deterministic by construction.
- (−) Breaking migration across theories/runtime/codegen/tests (accepted; R2 precedent — mechanical).
- (−) No in-IR time advancement means a single program cannot observe the clock moving; programs needing
  "elapsed" semantics take both instants as inputs. Revisit only with a named use case.
- (−) The single-source assumption is trust, not proof — named in the manifest, reviewed with the TCB.

## What this means for implementers
- Anti-vacuity for the boundary: theorems for get-at-deadline (live, `now = d`), get-past-deadline
  (absent, `now = d+1`), plus a mutant store using `<` (dead AT the deadline) whose observable behavior
  the statements reject. Inhabitance for a deadline-carrying store state.
- Keys inside the reference map: byte strings need an ordered key — use the stdlib string order over
  Coq strings (convert from the `list ascii` payloads at the op boundary); do NOT invent a new ordering.
- `OSetDeadline`'s second argument uses existing val forms (`VNone`/`VSome (VInt d)`) — no new val
  constructors in this milestone.
- The Time handler must be OUTSIDE the store handler in the composed runner (the store realizer may
  read the shared source directly; if it instead performs ONow, composition order is load-bearing).
- vm_compute + existentials: explicit witnesses (theories/Prims.v header — the OOM is real).
