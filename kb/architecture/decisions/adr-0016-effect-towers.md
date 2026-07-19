---
id: adr-0016-effect-towers
type: decision
summary: Effect towers — the 12 ops split into a 7-op kernel (plain Store get/put/delete, Now, Throw, Ask, Trace) and 5 derived ops (Expiry, Cache, Journal) given total Rocq elaborations into kernel programs with per-layer observational refinement theorems; codegen gains a kernel-only mode K exercised by CI; every manifest entry names its discharge path (kernel-irreducible vs discharged-by-theorem). High-level effects become proven implementations over a smaller trusted core — the descent path the TCB needs to be credible.
domain: architecture
last-updated: 2026-07-19
depends-on: [effir, adr-0001-first-order-ast, adr-0004-trust-model, adr-0011-time-and-expiring-store, adr-0013-journal-effect]
refines: []
related: [adr-0014-wf-checker, runtime-manifest, plan-towers, slice1-status, tower-rationale]
---
# ADR-0016 — Effect towers: kernel/derived split, proven elaborations, dischargeable trust

## Context
Design review 2026-07-19 (user, after reading rocqeteer + redoq): **(1)** the op list reads as
chosen-for-redoq — deadlines, cache, journal are Redis features promoted to *primitive* effects, which
undercuts the README's domain-independence claim to any skeptical reader; **(2)** the TCB is wide with no
descent path — pragmatic trust is acceptable (nobody re-verifies the OS from the application layer), but
each trusted entry should be *dischargeable in principle* by descending one abstraction level, given the
energy; **(3)** today's high-level effects should be *expressible as implementations* of lower-level ones.
This is the standard credibility structure of the strongest related work (certified abstraction layers /
CertiKOS; CakeML's verified stack). Hard constraint: invariant 1 — **one EffIR, two backends**; towers must
not smuggle a handler construct or a second program representation into the IR. Historical note: the
current op set is not an accident — adr-0006 mandated that the first application drive the effects; the
tower is the planned correction *after* that bet paid off, not a reversal of it.

## Decision
1. **Kernel/derived split (level 1).** The 12 ops partition into a **kernel** — `OGet`/`OPut`/`ODelete`
   *without* expiry semantics (a plain bytes→dval store), `ONow`, `OThrow`, `OAsk`, `OTrace` (7 ops, 5
   families) — and **derived** families: **Expiry** (`OGetDeadline`/`OSetDeadline` + the liveness aspect of
   the store ops), **Cache** (`OCacheGet`/`OCachePut`), **Journal** (`OJournal`). Derived ops stay in the IR
   unchanged (source programs and redoq are untouched); what changes is their *trust status*.
2. **Mechanism: elaboration + projection, not in-IR handlers.** Per derived family X, a **total Rocq
   function** `elab_X : tm -> tm` macro-expands each derived op into a kernel program fragment, plus a
   world projection `π_X` and one **refinement theorem**: for wf `p`,
   `observe_X (run p w) = observe_π (run (elab_X p) (π_X w))`. Towers are *theorems about programs*; the
   IR gains zero constructs (invariant 1 intact). Layers compose by function composition of elabs.
3. **The three elaborations.**
   - **Expiry** (flagship — the trickiest realizer semantics move from trusted OCaml into proven EffIR):
     kernel entries pack `DPair value (DSome (DInt d) | DNone)`; elaborated `OGet` = kernel get, `Match`
     the pair, compare `ONow` to `d` via `PCmpInt` (liveness `now <= d`, the adr-0011 boundary); `OPut`
     stores `DPair v DNone` (put clears the deadline); `OSetDeadline` = get-then-repack; lazy expiry
     (dead entries physically present in the kernel store) mirrors the runtime and is absorbed by `π`.
   - **Cache** *(corrected — see §Corrections)*: a **faithful store-backed elaboration** — cache entries
     live in the store under escaped keys; `runtime/cache.ml` becomes a performance option because the
     elaboration implements the same semantics over the kernel, not because cache reads are droppable.
   - **Journal** *(corrected — see §Corrections)*: append to an **escaped kernel key** (`PListSnoc` on a
     chronological `DList` of `DPair (DInt now) payload` at the journal key). No wf extension: key
     escaping (below) makes collision structurally impossible.
4. **Two execution modes, both differentially tested.** **Mode F** (fused — today's realizers, the
   production default; fast). **Mode K** (kernel-only): the pipeline runs `elab p` (elaboration happens in
   Rocq and is extracted, so codegen sees an ordinary kernel term), against a runtime containing **kernel
   realizers only**. CI runs the derived-effect differential suites in *both* modes. Mode K is a shippable
   configuration, not a thought experiment — it is what "we could descend if we had the energy" compiles to.
5. **The TCB report names every discharge path.** Each manifest family entry gains a `discharge` field:
   `kernel-v1` (irreducible at this level; dischargeable only by a future lower kernel) or
   `derived(<theorem>)` (discharged by a named, CI-checked refinement theorem + mode-K tests). The
   manifest schema, `tcb_report` generator, and a CI check (named theorems must exist and be axiom-free)
   are updated together. Wording discipline (adr-0004) extends: mode-F realizers remain *trusted and
   tested*; the claim is "**dischargeable**, with the discharge proven and CI-exercised" — never "TCB
   eliminated".
6. **The kernel is a level, not a floor.** When genuinely lower families land (byte-stream fd I/O for the
   Unix-tool app, sockets for the HTTP server, concurrency — see [[plan-towers]]), today's kernel families
   may themselves become derived. Each descent is its own ADR; the *discipline* (elab + refinement theorem
   + mode-K-style CI + discharge entry) is the invariant this ADR fixes.

## Consequences
- (+) Inverts the "effects were chosen for Redis" critique into a demonstrated feature: deadlines, cache,
  journal are *proven implementations over a 7-op kernel* — theorem attached. Pre-announcement credibility.
- (+) Irreducible trust shrinks from 12 op families to 7 kernel ops (mode K); the manifest's audit surface
  now distinguishes "must trust" from "may trust for speed".
- (+) Zero IR churn, zero redoq churn: source programs, proofs, and mode F behavior are unchanged.
- (−) The elaboration proofs are real work — expiry's simulation through `observe` with lazy expiry and
  journal's namespace discipline are the two known-hard spots (see [[plan-towers]] for sizing).
- (−) CI cost roughly doubles for derived-effect diff suites (both modes).
- (−) Mode F's fused realizers still need their differential validation against the reference — the tower
  adds obligations; it removes none (adr-0004's load-bearing tests stay load-bearing).

## What this means for implementers
- **Anti-vacuity per elaboration (adr-0005):** a mutant elaboration must break the refinement theorem —
  expiry with `<` liveness (mirror of the TimeStore mutant, now at the elaborated level); journal dropping
  or reordering an entry; cache "hit" returning a fabricated value. Plus inhabitance on deadline-carrying
  worlds.
- **Mode K in CI:** `diff_store`/`diff_cache`/`diff_journal` gain a mode-K run (reference vs
  kernel-runtime); coverage assertions unchanged. The freshness gate covers the extracted `elab_X`.
- Elaborated programs must pass the wf checker (adr-0014) by *construction* — state and prove
  `wf p -> wf (elab_X p)`; codegen's wf gate then needs no special case.
- Key escaping: the prefix constants are defined once in `theories/`, surfaced in the manifest; the
  observable projection strips them (untrusted harness code, like the expiry unpacking).

## Corrections (C2 design, 2026-07-19)
Two §3 decisions did not survive proof-design contact; recorded here per the house rule that ADRs match
what is provable, not what was hoped:
1. **The Cache null elaboration is UNSOUND for arbitrary programs.** `OCachePut k v; OCacheGet k` returns
   `DSome v` at the source but `DNone` under the null elaboration — outcome inequality from the empty
   cache. `cache_invisible` (hit ≡ miss) is a statement about coherent *use*, which EffIR does not
   enforce; an unconditional tower theorem therefore needs the **faithful** store-backed elaboration.
   The "cache is a performance effect" narrative survives at the REALIZER level, not the semantic one.
2. **The reserved-namespace wf extension cannot work syntactically.** Store keys are runtime values
   (env-supplied, computed via bytes prims); no syntactic checker can bound them, so a reserved-namespace
   side condition would be semantic, per-program, and unconditionality would be lost. Replaced by **total
   injective key ESCAPING inside the elaboration**: user store keys ↦ `"u" ++ k`, cache keys ↦ `"c" ++ k`,
   the journal ↦ `"j"` — first-byte discrimination partitions the kernel key space, collisions are
   structurally impossible, the theorem stays unconditional, and adr-0014 is untouched.
3. Consequently Cache and Journal (plus the escaping of the five store ops) form **one consolidation
   layer** `elab_ns` *below* the Expiry layer: mode K runs `elab_expiry ∘ elab_ns`, one artifact over the
   kernel realizer set {Store_kernel, Time, Throw, Ask, Trace} — no cache realizer, no journal realizer.
