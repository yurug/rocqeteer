# Rocqeteer — Ambiguity Resolution, Round 1 (domain-neutral)

**Correction note:** an earlier draft of this file wrongly threaded Tezos/Octez through the questions.
Rocqeteer is a **completely independent, domain-independent project** — a general toolchain for using Rocq
as a certified programming language. No application domain is assumed. This file has been rewritten
accordingly.

Phase 1 of the spec-driven methodology. Defaults encode the de-risked plan from
`kb/reports/premortem-idea-20260620.md`. **You don't have to fill in a form:** if the defaults look right,
just reply *"defaults are fine, proceed"* and I'll fold them into the Knowledge Base (Phase 2). Otherwise
correct only the ones you disagree with. The handful that genuinely need your judgment are marked 🔴.

---

## A. Scope & headline claim

**A1. 🔴 What does "nonfunctionally correct" mean for v1?** *(Your own goal says "functionally and
nonfunctionally correct" — this fork matters.)*
- **Default (A):** v1 **proves functional correctness** (equivalence of the generated program to a Rocq
  reference semantics, under explicitly-listed refinement axioms) and **measures** non-functional
  properties (latency, allocations, determinism) with CI regression gates. Formal *proofs* of cost/
  resource/time/space bounds are an explicit **research stretch for a later phase, not a v1 deliverable**.
- **Alternative (B):** make formal non-functional proofs (a cost semantics with proven resource bounds) a
  **first-class v1 goal** — substantially larger, research-grade, and it reshapes the architecture.
> Your answer:

**A2. 🟡 Is v1 scoped to standalone, self-contained certified programs (not retrofitting into an existing
large codebase)?**
Default: **Yes.** v1 produces self-contained certified components/programs. Embedding generated code into a
pre-existing large external codebase (with its own build, types, error monads, review culture) is out of
scope until the pipeline is proven on standalone code.
> Your answer:

**A3. 🔴 What is the "realistic" (non-toy) pilot that defines done for the MVP?** *(domain-neutral)*
- **Default:** a **verified binary serialization codec** — `encode`/`decode` with a proven round-trip
  (`decode (encode x) = Ok x`) in the reference model, generated to direct-style OCaml over `bytes`, and
  differentially tested. Universal, self-contained, and it exercises bytes + (later) GADTs without needing
  any application domain.
- Alternatives if you'd rather: a small **expression-language interpreter/evaluator**, or a **verified
  in-memory data structure** (e.g. a balanced map) behind an effectful API. Tell me if you have a specific
  example program in mind that you'd find compelling.
> Your answer:

**A4. 🟡 One-sentence north star — is this right?**
Default: *"A small, auditable trusted base that lets us write effectful programs in Rocq, prove them
correct against reference semantics, and run them as fast idiomatic OCaml 5 — with every trust expansion
named in a TCB report."* (Performance parity with handwritten OCaml is a goal, not a v1 guarantee.)
> Your answer:

---

## B. Core architecture (the premortem's central correction)

**B1. 🔴 Replace HOAS `Prog` with a single FIRST-ORDER AST shared by reference interpreter and codegen?**
Default: **Yes.** Drop the report's `Op : ∀X, E X → (X → Prog E A) → Prog E A` (HOAS continuation,
unserializable). Use an explicit-binder term language (`Ret`/`Bind`/`Let`/`Var`/`Perform`/`Match`) with
**de Bruijn indices** internally and a named-variable surface notation. The same AST is (a) interpreted in
Rocq for the reference, and (b) extracted to an OCaml ADT consumed directly by the codegen — structurally
guaranteeing "the program proved = the program run."
> Your answer:

**B2. 🔴 How does the AST get from Rocq to the codegen?**
Default: **Rocq extraction of the AST datatype to an OCaml ADT**, consumed in-process by the codegen — no
JSON/S-expression serialization layer in the v1 TCB. A textual export can be added later for tooling.
> Your answer:

**B3. 🔴 Dependency budget for v1: `rocq-stdlib` + `qcheck` + `zarith` only?**
Default: **Yes.** No `coq-itree`, `MetaRocq`, `coq-ext-lib`, `coq-equations`, `coq-malfunction` (none are
packaged for Rocq 9.1). An ITree bridge and MetaRocq-based "recognized Gallina" (Mode B) become optional
later modules, never MVP blockers.
> Your answer:

**B4. 🟡 Mode A only for v1 (deep first-order DSL + notation); Mode B (monadic Gallina via MetaRocq) deferred?**
Default: **Yes**, as the report itself recommends.
> Your answer:

---

## C. Effects, fragment & data

**C1. 🟡 Which effect goes through the full pipeline first?**
Default: **KV state only** (`Get`/`Put`/`Delete`) end-to-end (prove → extract → codegen → differential
test → green) before any second effect. Then `Error`, then `Env`/`Trace`/`Cache`.
> Your answer:

**C2. 🟡 Recursion in v1?**
Default: structural recursion over lists/trees + bounded `int` loops + fuel-based well-founded recursion;
**no cofixpoints**. Slice 1 (KV `incr`) needs none.
> Your answer:

**C3. 🟢 Multi-shot continuations banned in v1 (one-shot resume only)?**
Default: **Yes** (OCaml 5 continuations are one-shot). Backtracking/nondeterminism, if ever needed,
compiles to explicit lists/streams, never via duplicated continuations.
> Your answer:

**C4. 🔴 Integer/value model — how do we avoid the silent overflow-divergence trap (failure #3)?**
Default: keep `key`/`value` **abstract** in slice 1 (Rocq `Parameter`s realized to concrete OCaml types via
the manifest). When arithmetic enters, model values as **`Z` (zarith)** in the reference and realize to a
**`Z`/zarith** runtime by default (exactness over speed first); a bounded `int63` realizer with *proven or
checked* overflow bounds is an opt-in, separately-reviewed realizer — never the silent default.
> Your answer:

---

## D. Trust, proofs & testing discipline

**D1. 🔴 Anti-vacuity gates for every spec (fights failure #6: vacuous proofs)?**
Default: **Yes.** Every Hoare spec ships (a) an **inhabitance lemma** (`∃ s, pre s`) proving the
precondition is satisfiable, and (b) a **proof-mutation test** — negate a postcondition or plug a
known-bad implementation and confirm the proof *fails*. Review checks theorem *statements*, not names.
> Your answer:

**D2. 🟢 CI hard-fail conditions?**
Default: build fails on any `Admitted`/`admit`/new `Axiom` without a review label; any `Obj.magic` outside
the one approved witness module; any `Effect.perform` outside generated/runtime modules; any unregistered
`Extract Constant`; any manually-edited generated file; any public entrypoint missing a differential test.
A `tcb_report.md` is generated and diffed each build.
> Your answer:

**D3. 🔴 Differential-test generator policy (fights failure #3: false assurance)?**
Default: generators are **boundary-/adversary-biased** (integer extremes, overflow neighborhoods, hash
collisions, empty/large/duplicate inputs), with **seed replay** and a **failing-input corpus** committed on
every discovered divergence. Uniform-random-only generation is disallowed for trusted entrypoints.
> Your answer:

**D4. 🟢 Exact wording of the "certified" claim?**
Default: *"Functional equivalence to a Rocq reference model is machine-checked, under the refinement axioms
listed in the TCB manifest. The OCaml compiler, runtime, effect handlers, and native realizers are trusted
and differentially tested, not proven."* Nothing is called "certified" without that qualifier nearby.
> Your answer:

---

## E. Process, repo & deliverables

**E1. 🔴 Vertical-slice discipline: no breadth until one example is green end-to-end (fights failure #5)?**
Default: **Yes.** No second effect family, runtime module, or codegen feature starts until the KV slice
goes cleanly Rocq-proof → extracted reference → generated fast OCaml → boundary-biased differential test,
all green and committed. "Green end-to-end examples" must be ≥1 before breadth.
> Your answer:

**E2. 🟢 Git: initialize a local repo now; name + remote?**
Default: initialize a **local git repo now** (per your "everything on git" principle); name **`rocqeteer`**;
create a remote (private GitHub) **only when you ask**. Is `rocqeteer` the name you want?
> Your answer:

**E3. 🟢 License?**
Default: **MIT**, with generated-file headers carrying source path + manifest/contract hashes + "do not
edit". Change if you need a different license.
> Your answer:

**E4. 🟢 Repo layout — report's §14 (`theories/ codegen/ runtime/ generated/ tests/ bench/ ci/ docs/`) + `kb/`, created lazily per phase?**
Default: **Yes**, directories created only as a phase needs them.
> Your answer:

---

## F. Anything I missed

**F1.** Constraints, preferences, prior art, or hard requirements I haven't asked about — e.g. a specific
example program you want to see verified, a deadline or demo, an existing Rocq development this should
interoperate with, or coding-style rules beyond the methodology defaults?
> Your answer:
</content>
