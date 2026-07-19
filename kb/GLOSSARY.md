---
id: glossary
type: glossary
summary: Canonical names and one-line definitions for every Rocqeteer domain term; the controlled vocabulary for KB tags.
domain: meta
last-updated: 2026-07-19
depends-on: []
refines: []
related: [index, prd, arch-overview]
---
# Glossary — Rocqeteer

## One-liner
Canonical vocabulary. Every KB file's `tags` and prose draw from these terms; use the exact spelling here.

## Terms

- **Rocq** — the proof assistant formerly named Coq (we run **9.1.1**). Its term/spec language is **Gallina**.
- **Effectful program** — a computation that performs operations (state, error, …) rather than only returning a value.
- **Effect signature** — a type-indexed family of operations, e.g. `KV : Type -> Type` with `Get`/`Put`/`Delete`. The operation's return type is part of its constructor type.
- **EffIR** — *Effect Intermediate Representation*: Rocqeteer's **first-order, explicit-binder** term language (de Bruijn indices). It is the **single** representation that the reference interpreter evaluates and the codegen lowers. See [[effir]].
- **`val` / `tm`** — EffIR's two layers: `val` = pure first-order expressions (no effects); `tm` = effectful computations (`Ret`/`Bind`/`Perform`/`Match`).
- **Reference semantics / reference interpreter** — a pure Rocq function that runs an EffIR `tm` against a pure handler. It is the **proof target** and the **test oracle**. See [[reference-semantics]].
- **Fast / generated code** — the idiomatic direct-style **OCaml 5** emitted by the codegen for the same EffIR. The thing actually run in production. See [[codegen]].
- **Codegen (`rocq-eff-codegen`)** — the trusted OCaml tool that lowers EffIR (delivered as an extracted OCaml ADT) to direct-style OCaml. Part of the TCB. See [[codegen]].
- **Realizer** — a mapping from a Rocq abstract type/operation to a concrete OCaml implementation, declared in the **runtime manifest** with a contract and tests. See [[runtime-manifest]].
- **Runtime manifest** — machine-readable registry of every realizer (Rocq name → OCaml symbol, purity, pre/post, tests, owner). The audit surface for trust. See [[runtime-manifest]].
- **Refinement axiom** — an *unproven* Rocq `Axiom` asserting the OCaml runtime observably refines the reference semantics. Explicitly listed in the TCB report; validated only by differential tests. See [[adr-0004-trust-model]].
- **TCB (Trusted Computing Base)** — everything that must be correct for results to hold. Split into proof-TCB, extraction/runtime-TCB, system-TCB. See [[arch-overview]].
- **TCB report** — generated `docs/tcb_report.md` listing Rocq/OCaml versions, axioms (`Print Assumptions`), `Obj.magic` uses, `Extract Constant`s, entrypoints. Diffed in CI.
- **Differential testing** — running reference vs fast on the same generated inputs and asserting normalized-equal outputs. The primary check on the refinement axiom. See [[conv-testing-strategy]].
- **Anti-vacuity discipline** — proof hygiene that prevents trivially-true specs: an **inhabitance lemma** (`∃ s, pre s`) per Hoare spec plus a **proof-mutation test** (a deliberately-wrong impl must break the proof). See [[adr-0005-anti-vacuity]].
- **Hoare spec** — a `{ pre; post }` record over a state and result; `verifies p spec` means running `p` from any `pre` state lands in `post`. See [[reference-semantics]].
- **Deep handler** — OCaml 5 `Effect.Deep` handler that reinstalls itself across `continue`; used for first-order effects. One-shot continuation only. See [[ext-ocaml5-effects]].
- **One-shot continuation** — an OCaml 5 continuation resumable **at most once**; resuming twice raises `Continuation_already_resumed`. v1 bans multi-shot.
- **Vertical slice** — one example carried end-to-end (Rocq proof → extracted reference → generated OCaml → green differential test) before any breadth is added. v1's first slice is **KV**. See [[adr-0006-vertical-slice]].
- **KV effect** — the first effect family: `Get`/`Put`/`Delete` over an abstract key/value map. The slice-1 example.
- **Codec (pilot)** — the realistic non-toy MVP target: a verified binary serialization `encode`/`decode` with a proven round-trip. See [[prd]].
- **Mode A / Mode B** — A = deep first-order DSL with notation (v1). B = recognized monadic Gallina lowered via MetaRocq (deferred). See [[adr-0001-first-order-ast]].
- **Effect tower** — the layering discipline: a **derived** effect is given a proven **elaboration** into programs over lower (**kernel**) effects, with a per-layer refinement theorem. Towers are theorems about programs; the IR gains no constructs. See [[adr-0016-effect-towers]].
- **Kernel / derived effect** — kernel = an op family whose realizer is irreducibly trusted at the current level (v1: plain Store, Now, Throw, Ask, Trace); derived = an op family discharged by an elaboration theorem (v1: Expiry, Cache, Journal). See [[adr-0016-effect-towers]].
- **Elaboration (`elab_X`)** — a total Rocq function `tm -> tm` macro-expanding a derived family's ops into kernel fragments; extracted, so mode K composes it before codegen. See [[adr-0016-effect-towers]].
- **Mode F / Mode K** — F = fused execution with the full realizer set (production default); K = kernel-only execution of the elaborated program against kernel realizers only. Both differentially tested in CI. See [[adr-0016-effect-towers]].
- **Discharge path** — the manifest/TCB-report field stating how a trusted entry could stop being trusted: `kernel-v1` (needs a future lower kernel) or `derived(<theorem>)` (already proven; the realizer is a performance option). See [[adr-0016-effect-towers]].

## Agent notes
> When a term here gains a dedicated file, link it with a wiki-style double-bracket reference to that file's id. Treat `EffIR`, `realizer`, `refinement axiom`, and `differential testing` as load-bearing — most design decisions reduce to them.

## Related files
- `INDEX.md` — KB routing table and quick-load bundles.
- `domain/prd.md` — what we are building and the resolved scope decisions.
</content>
