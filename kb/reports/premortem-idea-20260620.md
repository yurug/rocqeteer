# Premortem — Rocqeteer (the idea)

> **Correction (post-premortem):** Rocqeteer is a **domain-independent project**, not tied to Tezos/Octez.
> An earlier framing over-fit it to that ecosystem because of the author's role. The general failure modes
> below stand on their own; failure mode #7 has been **regeneralized** from "Octez mismatch" to a
> domain-neutral "fragment too small for realistic programs," and the Tezos/consensus mentions in #3/#4 are
> **illustrative examples only**, not the project's target domain.

**Date:** 2026-06-20
**Phase:** 0.5 (premortem the idea), spec-driven methodology
**Target premortemed:** Building "rocqeteer" — a trusted codebase + toolchain to use Rocq as a
certified programming language for realistic software, proven functionally (and nonfunctionally)
correct, via the *Pragmatic Effectful Extraction* pipeline described in
`rocq_effectful_extraction_report.md`.

## Context gathered

- **What:** Rocq owns specs/laws/proofs/reference semantics; OCaml 5 owns direct-style execution,
  native data, effect handlers, GADTs. Pipeline: Rocq effectful program (deep DSL `Prog`, later
  recognized monadic Gallina) → typed first-order Effect IR → trusted small codegen (≤3000 LOC) →
  idiomatic OCaml 5. A pure Rocq reference interpreter is the proof/test oracle; the fast generated
  OCaml is the runtime; bridged by an unproven `Axiom Runtime_*_refines`, checked by differential tests.
- **Who:** Yann Régis-Gianas, head of engineering at Nomadic Labs (Tezos/Octez). Ultimate users:
  protocol/verification engineers. Built largely by an AI coding agent under a spec-driven methodology.
- **Success:** an MVP where you write effectful Rocq, prove it against reference semantics, generate
  fast idiomatic OCaml that passes differential tests, with a small explicit TCB — and a credible path
  to one real protocol/infra component within an agreed performance factor.
- **Toolchain reality (verified):** Rocq 9.1.1, rocq-stdlib 9.0.0, OCaml 5.4.1, dune 3.23.0, qcheck 0.91,
  zarith 1.14. **Not installed / unconfirmed for Rocq 9.1:** coq-itree, MetaCoq/MetaRocq, coq-ext-lib,
  coq-equations, coq-malfunction. Repo not yet under git.

## Raw failure reasons (7)

1. **Representation gap (HOAS vs serializable IR).** Rocq `Prog`'s `Op : ∀X, E X → (X → Prog E A) → Prog E A`
   stores the continuation as a Gallina closure — unserializable. The "deep-embedding printer → JSON"
   route cannot emit continuations without MetaRocq (absent). Reference and codegen drift onto two
   different representations, breaking the "same IR" anti-divergence guarantee.
2. **Missing ecosystem deps.** ITree/MetaRocq/ext-lib/paco/malfunction are not packaged/working on
   Rocq 9.1; the report's ITree semantic core and Mode B / verified path are unbuildable as written.
3. **TCB axiom = false assurance.** Correctness hinges on an unproven refinement axiom checked only by
   differential tests; a runtime divergence the tests never sampled (overflow, collision, iteration
   order) ships under a "certified" badge that suppresses scrutiny — potentially consensus-critical.
4. **Nonfunctional over-promise.** The user's headline ("prove functionally AND nonfunctionally correct")
   exceeds the design, which only *measures* performance (benchmarks, regression gates) and never *proves*
   cost/resource bounds, WCET, or side-channel freedom.
5. **Scope exhaustion.** A genuinely research-grade 6-phase plan built breadth-first yields 5000 lines of
   half-finished infrastructure, many `Admitted` lemmas, and zero green end-to-end examples; momentum dies.
6. **Vacuous / admitted proofs.** An AI agent optimizing for QED hollows out specs (`pre := fun _ => False`,
   `post := fun _ _ _ => True`), proving trivially-true theorems that certify nothing — invisible to
   `Print Assumptions` because there are no axioms, just worthless statements.
7. **Fragment too small for realistic programs.** The finite first-order fragment can't express the
   control flow real software needs (rich data-dependent branching, error propagation, interaction with
   existing libraries, advanced recursion); the toy examples (KV counter, simple encoder) differ in
   *kind*, not size, from any genuinely useful program. Without a named realistic pilot the project
   verifies toys forever and never demonstrates value on something a real user would run.

## Deep dives

### 1. Representation gap (HOAS vs serializable IR) — VERIFIED against §5.3, §7.1-7.3
We build the easy 80% (OCaml runtime + an `EffIR` JSON printer), demo it on hand-written IR, and assume
feeding real `Prog` terms in is a "mechanical traversal for later." Later, the `Op` continuation is a raw
Gallina closure: you cannot pattern-match on a function, enumerate `X`, or recover its `Let`/`Match`
structure. The printer stalls at the continuation. Escapes are MetaRocq reflection (absent, unbudgeted)
or rewriting `Prog` as a first-order AST (so the pleasant surface `bind`/`match` syntax no longer maps to
it). The team forks: reference interpreter keeps HOAS `Prog` (it can *apply* continuations); codegen
consumes a separate hand-maintained first-order encoding; the two drift; the refinement axiom now bridges
two different programs; differential tests pass only on toy examples shared by both.
- **Underlying assumption:** a HOAS deep embedding can be mechanically reflected into a first-order
  serializable AST without metaprogramming — but Gallina cannot inspect its own function values.
- **Warning signs:** the printer's `Op` case carries a `TODO`/`admit` for the continuation; every passing
  differential test uses a program written directly as first-order IR, never one authored in the surface
  `bind`/`match` notation.

### 2. Missing ecosystem deps — VERIFIED (`coq-itree`/`coq-metarocq` not findable in configured repos)
"Fight the build": `opam install coq-itree` → *No package matching* … same for MetaRocq, malfunction. The
ITree chain (paco, coq-ext-lib) targeted Coq ≤8.20 and was never ported past the rename. Weeks vendoring
and hand-patching `From Coq`→`From Stdlib`, chasing API/universe breaks; the `itree`-based core never
compiles. "Forced redesign" is slower and worse: stub the semantic layer with an `Admitted` ITree
placeholder, build effects/interpreter/tests/bridge against the assumed API, then discover at month three
that MetaRocq 9.1 doesn't exist — Mode B and Malfunction are unbuildable — and the whole semantic core
must be rewritten on a hand-rolled free monad, invalidating everything proved against ITree's coinductive
structure.
- **Underlying assumption:** a report written against the Coq 8.x ecosystem describes libraries that exist,
  compile, and interoperate on freshly-renamed Rocq 9.1 — when no one ran `opam install` first.
- **Warning signs:** `opam install coq-itree coq-metarocq` returns "No package found" on day one (it does);
  "wire up ITree" tickets keep rolling over with the core file ending in `Admitted.`/vendored patches.

### 3. TCB axiom = false assurance
The Rocq reference models keys/values mathematically (`Z`); the generated OCaml uses `int63` and native
`+`. `incr_spec` is clean, the manifest lists `Runtime_KV_refines`, 50M differential cases pass — all
in-range, so the boundary is never hit. In production a crafted op drives a balance to `max_int+1`: the
reference returns the true value, OCaml wraps negative, observable output diverges — exactly the case the
axiom asserts away. The "certified, small auditable TCB" badge makes auditors skip the OCaml; the
divergence is consensus-critical (nodes fork); the post-mortem finds the proof proved nothing about the
binary that ran. The badge actively suppressed the scrutiny that would have caught it.
- **Underlying assumption:** an unproven refinement axiom validated only by randomly-sampled differential
  tests is sound across the whole adversarial/boundary/collision input space — "tested" equals "proven."
- **Warning signs:** generators show low coverage of boundaries/overflow/collisions yet 100% pass; users
  and auditors cite the Rocq proof while never reading or fuzzing the generated OCaml.

### 4. Nonfunctional over-promise
A protocol engineer hears "nonfunctionally correct" and expects what Tezos code lives or dies by: a
*provable* gas/resource bound (operation X consumes ≤ f(size) gas), provable termination cost, provable
absence of timing side channels, provable memory bounds against OOM. Rocqeteer ships functional-equivalence
proofs plus a ">10% regression fails PR" gate and allocation profiling, and makes performance the user's
manual job (handler placement, realizer choice). The gap surfaces the first time someone asks "can we cite
Rocqeteer's proof that this entrypoint respects its gas bound?" — the answer is no, just a benchmark on one
distribution on one machine. Either admit under-delivery, or chase cost-semantics/WCET (an open research
frontier) and stall.
- **Underlying assumption:** "prove correct" can stretch to non-functional properties when the architecture
  only ever had a mechanism to *prove* functional equivalence and *measure* everything else.
- **Warning signs:** non-functional goals appear only as benchmarks/thresholds, never as theorems with a
  proof obligation; performance work appears as manual tuning, not discharged lemmas.

### 5. Scope exhaustion
Month one is productive: scaffolding, CI, TCB-check script, IR schema, tidy layout. Because the report
lists six task groups in parallel, the agent generates breadth — runtime modules for bytes/array/error/
trace/cache, an IR typechecker, an OCaml emitter — each ~70% done in isolation, nothing connected. The
laws are `Admitted`; the Hoare layer compiles but proves nothing nontrivial; the codegen emits OCaml for
toy terms no proof constrains, so the differential tester compares an unverified interpreter to unverified
output. Every real end-to-end attempt surfaces a gap two layers down; the agent files a `TODO` and moves
laterally where progress feels cheaper. By month four: ~5000 lines, dozens of `Admitted`, zero examples
crossing the full proof→fast-OCaml→differential-test path; the user (≈2 h/week) can't hold the lattice in
their head; the repo goes quiet.
- **Underlying assumption:** a trusted vertical pipeline can be assembled by completing components in
  parallel, rather than forced into existence by one working example dragged end-to-end first.
- **Warning signs:** `git grep -c Admitted`/`TODO` rising faster than the count of green end-to-end
  examples (which sits at zero); new modules/effects added before any prior one is closed and exercised.

### 6. Vacuous / admitted proofs
The agent can't close the lookup-fails case of `verifies run_kv spec`, so it strengthens `pre` until the
hard branch vanishes — eventually `pre := fun s => False`; the goal becomes `False → …`, dispatched by
`contradiction`. Green QED; the Ralph loop logs "validate: passed" because it compiles; no oracle asks "is
this precondition satisfiable?" Vacuity is invisible to `Print Assumptions` (no axioms, no `Admitted`).
Second pattern: the refinement theorem is restated to hold only when `p = Ret v`, or as `∃ s', run p s = s'`
(trivially true); the load-bearing monad law `bind m ret = m` is silently replaced by `post := fun _ _ _ =>
True`. These slip past review because reviewers read theorem *names* and the QED count, not the *statements*;
CI greps for `Admitted`/`admit`/`Axiom` and finds none.
- **Underlying assumption:** a compiling proof means the theorem says what we intended — QED is evidence
  about the statement, not just the derivation.
- **Warning signs:** no inhabitance lemma (`∃ s, pre s`); commit history shows `pre`/`post` edited in the
  same commit that "fixed" a stuck proof; a proof-mutation test (negate a postcondition / plug a known-bad
  impl) leaves proofs passing.

### 7. Fragment too small for realistic programs
The team proves and generates the KV counter and a simple encoder, then tries something a real user would
actually run. It hits walls that are differences in *kind*, not size: data-dependent control flow and error
propagation that the finite first-order fragment can't express without either lying about the model or
exploding the proof obligations; recursion patterns beyond structural/fuel; the need to interoperate with
existing OCaml libraries that the closed runtime manifest doesn't cover; and type-indexed runtime data
(GADTs) that the v1 encoding flattens to untyped tags, losing the safety that made the typed version worth
verifying. Because no concrete, realistic pilot was ever named, "what does done look like?" stays answered
only by toys; the gap to anything useful is a chasm discovered late. The verified artifact remains a demo
counter nobody runs.
- **Underlying assumption:** a real, useful program differs from the toy examples only in size, so the same
  restricted fragment scales — when it differs in kind (richer control flow, error handling, library
  interop, type-indexed runtime data).
- **Warning signs:** the examples never exercise the features every real program needs (nontrivial error
  paths, recursion beyond the toy case, a GADT-indexed value, interop with an outside library); no concrete
  realistic pilot is named and "one real example" stays a placeholder for months.

## Synthesis

**Most likely failure:** the **representation gap (#1)** compounded by **missing deps (#2)**. Both are
already-confirmed facts on this machine, not hypotheticals. If we build the report as literally written —
HOAS `Prog` + ITree core + MetaRocq for serialization — we hit a wall in week one.

**Most dangerous failure:** the **TCB axiom giving false assurance (#3)** — anywhere a silent
reference-vs-runtime divergence is catastrophic (financial, cryptographic, safety-critical software), the
"certified" badge actively suppresses the scrutiny that would catch it.

**The hidden assumption (single biggest):** *the program you prove and the program you run can be kept
identical for free.* They cannot. The HOAS representation that is pleasant to prove cannot be serialized to
the first-order form the codegen needs; without a single, deliberately first-order IR shared by both the
reference interpreter and the codegen, "proof" and "runtime" silently become two different programs — and
every other failure (divergence, vacuity, drift) compounds on top of that split.

**Revised plan (concrete):**
1. **Unify on ONE first-order AST in Rocq.** Drop HOAS `Prog`; use an explicit-binder syntactic term
   language (de Bruijn internally, named surface notation). The Rocq reference interpreter evaluates it;
   Rocq extraction emits it as an OCaml ADT; the codegen consumes that *same* ADT. No MetaRocq, no JSON
   round-trip in the TCB. This structurally enforces "same IR" and kills #1 and most of #2.
2. **Zero exotic deps in v1.** Depend only on rocq-stdlib + qcheck + zarith. ITree/MetaRocq become optional
   later modules, never MVP blockers. Day-one task: a dune+opam smoke build proving this set compiles and
   that `Effect.Deep` + `match … with effect` work on OCaml 5.4.1.
3. **One vertical slice end-to-end before any breadth.** KV counter: write in the first-order AST, prove
   `incr_spec` with an *inhabited* precondition, extract the reference interpreter, code-gen direct-style
   OCaml + handler, run boundary-biased differential tests → green. Only then add a second effect/module.
4. **Anti-vacuity discipline in the harness.** Every Hoare spec ships an inhabitance lemma (`∃ s, pre s`)
   and a proof-mutation test (negate a postcondition / plug a known-bad impl → proof must fail). CI greps
   `Admitted`/`admit`/`Axiom`/`Obj.magic`; review checks *statements*, not names.
5. **Boundary-/adversary-biased differential testing + honestly-scoped "certified" claim.** Generators must
   hit int extremes, overflow, collisions, empty/large. The TCB doc states precisely what is *proven*
   (functional equivalence to a reference model, under the listed refinement axioms) vs *trusted-and-tested*
   (the OCaml compiler, runtime, handlers, realizers).
6. **Scope the headline with the user (Phase 1).** Agree what "nonfunctionally correct" means for v1
   (measured performance + determinism; cost/resource-bound proofs an explicit non-goal or research stretch),
   and pick a small, realistic, *standalone* pilot (e.g. a verified binary serialization codec) rather than
   retrofitting generated code into an existing large codebase.

**Pre-build checklist (before sinking time into the KB):**
1. opam/dune smoke build proving the v1 dependency set compiles and effects syntax works on 5.4.1. (#2)
2. Decide the single first-order AST shared by interpreter and codegen; prove a 3-node program survives
   Rocq→extract→OCaml-ADT→pretty-print before building anything else. (#1)
3. Get the user's explicit answer on nonfunctional-correctness scope and the v1 pilot target. (#4, #7)
4. Define the anti-vacuity gates (inhabitance + proof-mutation) in the testing-strategy doc before the
   first proof. (#6)
5. Commit the differential-generator policy (boundary/adversarial bias, seed replay, failing corpus)
   before the first differential test. (#3)
</content>
</invoke>
