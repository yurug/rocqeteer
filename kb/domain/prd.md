---
id: prd
type: spec
summary: Rocqeteer is a domain-independent trusted toolchain to write effectful programs in Rocq, prove them against reference semantics, and run them as fast idiomatic OCaml 5 with a small explicit TCB.
domain: product
last-updated: 2026-07-08
depends-on: [glossary]
refines: []
related: [arch-overview, prop-functional, prop-non-functional, adr-0004-trust-model, adr-0006-vertical-slice]
---
# PRD — Rocqeteer

## One-liner
A small, auditable trusted base that lets us write effectful programs in Rocq, **prove** them correct
against reference semantics, and **run** them as fast idiomatic OCaml 5 — with every trust expansion named
in a TCB report. (North star, confirmed Phase 1 / A4.)

## Scope
This is a **completely independent, domain-independent project**. No application domain is assumed; the
report's Tezos/Octez mentions were illustrative and are out of scope. "Realistic software systems" means
general software. Built largely by an AI agent under the spec-driven methodology in `agentic-dev-kit/`.

## Goals (from report §2, as resolved in Phase 1)
- **G1. Program with effects in Rocq** — KV/state, error, env, trace, cache.
- **G2. Reason in Rocq** — pure reference semantics, algebraic laws, Hoare specs, refinement vs handlers.
- **G3. Generate idiomatic OCaml** — direct-style OCaml 5 with `perform`, deep handlers, refs/arrays/bytes/Hashtbl, GADTs. No free-monad interpreter in hot paths.
- **G4. Keep the TCB explicit** — small, named, reviewed, measured; every expansion in the TCB report.
- **G5. Preserve engineering ergonomics** — generated OCaml looks like good OCaml and interops with libraries.
- **G6. Support performance work** — expose enough control to optimize allocation, boxing, arrays, bytes, handler placement.

## Non-functional expectation: MEASURED, not proven (Phase 1 / A1 = "measure")
v1 **proves functional correctness** (equivalence to a Rocq reference model, under listed refinement
axioms) and **measures** non-functional properties — latency, allocations, determinism — with CI
regression gates. **Formal proofs of cost / resource / time / space bounds are an explicit non-goal for
v1**, recorded as a research stretch for a later phase. See [[prop-non-functional]] and [[adr-0004-trust-model]].

## Users & user stories
Primary user: a verification engineer who wants certified-yet-fast components.
- *As an engineer, I write an effectful program in Rocq's first-order DSL and prove a Hoare spec about it.*
- *I run a single command to extract the reference interpreter and generate fast OCaml for the same program.*
- *CI shows me a differential test (reference vs fast) passing on adversarial inputs, and a TCB report naming every axiom and realizer my program relies on.*
- *I can read the generated OCaml and see idiomatic effect handlers, not a monad interpreter.*

## Deliverables
- **Slice 1 (MVP core):** the **KV** effect carried end-to-end — Rocq `incr` program + reference handler +
  proven `incr_spec` (with inhabitance lemma) → extracted reference → generated direct-style OCaml + deep
  handler → boundary-biased differential test green. See [[adr-0006-vertical-slice]].
- **Pilot (realistic, defines "done" for MVP):** a **verified binary serialization codec** — `encode`/`decode`
  over `bytes` with a proven round-trip `decode (encode x) = Ok x` in the reference model, generated to
  direct-style OCaml, differentially tested. Domain-neutral; exercises bytes and (later) GADTs. (A3.)

## Out of scope (v1)
- Compiling arbitrary Gallina (Mode B / MetaRocq) — deferred. [[adr-0001-first-order-ast]]
- ITree / coinductive semantics on hot paths; cofixpoints.
- Multi-shot continuations / backtracking via duplicated continuations. [[ext-ocaml5-effects]]
- Proving non-functional properties (cost/WCET/space). [[prop-non-functional]]
- Retrofitting generated code into an existing large external codebase (v1 = standalone components). (A2.)
- Arbitrary `Obj.magic`; unregistered `Extract Constant`; C stubs. [[adr-0004-trust-model]]

## Success criteria (MVP acceptance — adapted from report Appendix A)
1. First-order DSL supports `Ret`/`Bind`/`Perform`/`Match` and the slice's needs. [[effir]]
2. KV (and later Error/Env/Trace) effects defined in Rocq with pure reference handlers + basic laws.
3. At least one nontrivial example has a Rocq proof against reference semantics, with an inhabitance lemma.
4. EffIR reaches the codegen deterministically (via extraction). [[adr-0002-extraction-bridge]]
5. Codegen emits direct-style OCaml (no `Bind` constructors / free-monad interpreter in output).
6. Generated OCaml + handlers compile under OCaml 5.4.1.
7. Reference and fast pass boundary-biased differential tests. [[conv-testing-strategy]]
8. `docs/tcb_report.md` generated and diffed in CI; `Obj.magic` absent or isolated to one reviewed module.
9. No unregistered `Extract Constant`; public entrypoints catch unhandled effects.

## Agent notes
> The headline word is **measured**, not proven, for performance — do not let any doc or claim imply we
> *prove* non-functional correctness in v1. The riskiest design decision is the EffIR representation
> ([[adr-0001-first-order-ast]]); everything downstream assumes one first-order AST shared by interpreter
> and codegen.

## Related files
- `architecture/overview.md` — how the pieces fit and the TCB layering.
- `properties/INDEX.md` — the functional invariants (proven) and non-functional criteria (measured).
- `reports/premortem-idea-20260620.md` — the failure modes these decisions defend against.
</content>
