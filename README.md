# Rocqeteer

**Use Rocq as a certified programming language: write effectful programs in Rocq, *prove* them against
reference semantics, and *run* them as fast, idiomatic OCaml 5 — with a small, explicit, auditable trust
base.**

Rocqeteer is a domain-independent toolchain. Rocq owns the specifications, laws, and proofs; OCaml owns the
runtime — native data, effect handlers, direct-style execution. One first-order intermediate representation
(**EffIR**) is shared by the Rocq reference interpreter and the OCaml code generator, so *the program you
prove and the program you run cannot silently become different programs*.

> **Status:** IR v2 is complete (16 effect operations across nine families — including the C3 file
> family with its proven wc tool — general `Match`, `Fold`, 16 checked primitives,
> a well-formedness checker, and a weakest-precondition program logic — 413 closed theorems, zero
> axioms), and the toolchain has its first real consumer: **redoq**, a Redis-compatible server whose
> 22 data commands, RESP codecs and append-only-file recovery are proven with exactly these tools.
> Built with the spec-driven methodology in `agentic-dev-kit/`. The full design rationale, decisions, and
> the premortem that shaped them live in the knowledge base — start at [`kb/INDEX.md`](kb/INDEX.md).

## What it does (the slice)

You write an effectful program in Rocq as an EffIR term (e.g. "increment the counter at key *k*"), prove a
Hoare spec about it against a pure reference interpreter, and a single command:

1. **extracts** the reference interpreter to OCaml (the slow, faithful oracle), and
2. **generates** idiomatic direct-style OCaml 5 for the *same* term (the fast path: `Effect.perform` +
   deep handlers + a `Hashtbl`, no monad interpreter), then
3. **differentially tests** the two against each other on thousands of adversarial inputs, and
4. emits a **TCB report** naming every trust assumption.

```
Rocq EffIR term ──extract──▶ reference interpreter ─┐
       │                                            ├─▶ differential test (ref == fast?) ─▶ TCB report
       └──────codegen──────▶ direct-style OCaml ────┘
```

## The effects

Sixteen operations over one explicit `world`, grouped into nine effect families. Every family has a
compiled, proven example in the **[effects gallery](examples/README.md)** (`examples/` builds with
`make all`, so the gallery cannot rot), and a theory file with the general laws.

| Effect | Ops | One line | Tower | Gallery |
|---|---|---|---|---|
| **Keyed store** | `OGet` · `OPut` · `ODelete` | bytes-keyed state; per-key frame clauses | kernel | [`KeyedStore.v`](examples/KeyedStore.v) |
| **Expiry** | `OSetDeadline` · `OGetDeadline` | per-binding TTLs; live iff `now ≤ deadline` — expired = absent | **derived** ([`Elab.v`](theories/Elab.v)) | [`Expiry.v`](examples/Expiry.v) |
| **Time** | `ONow` | one injected instant per run: deterministic by construction, replayable | kernel | [`Clock.v`](examples/Clock.v) |
| **Errors** | `OThrow` | aborting exceptions with *structured* payloads; pre-throw effects commit | kernel | [`Throw.v`](examples/Throw.v) |
| **Environment** | `OAsk` | the Reader: immutable request/config context | kernel | [`Ask.v`](examples/Ask.v) |
| **Trace** | `OTrace` | the Writer: provable, ordered, structured logging | kernel | [`Tracing.v`](examples/Tracing.v) |
| **Cache** | `OCacheGet` · `OCachePut` | a memo table invisible to the observable — "only an optimization" is structural | **derived** ([`ElabNs.v`](theories/ElabNs.v)) | [`Memo.v`](examples/Memo.v) |
| **Journal** | `OJournal` | write-only timestamped log; a proven frame law makes durability an afterthought | **derived** ([`ElabNs.v`](theories/ElabNs.v)) | [`Journaling.v`](examples/Journaling.v) |
| **Files** | `OOpen` · `ORead` · `OFWrite` · `OClose` | byte streams over descriptors on a pure in-world FS; EOF = the empty chunk; modeled errors are values; the OS seam is named & runtime-checked | kernel ([ADR-0017](kb/architecture/decisions/adr-0017-file-io.md)) | [`Files.v`](examples/Files.v) |

**Effect towers.** The *derived* families are not irreducible trust: each has a proven
*elaboration* into programs over the kernel families (plain never-expiring store, clock,
errors, environment, trace, files) with a machine-checked refinement theorem per layer
(`Elab.elab_simulates`, `ElabNs.elab_ns_simulates` — axiom-free, no side conditions). A build can
therefore run in **mode K**: the elaborated programs against kernel realizers only — no deadline
logic, no cache realizer, no journal realizer in the trusted runtime — and CI differentially tests
that configuration on every commit (`diff_store_k`, `diff_cache_k`, `diff_journal_k`). The fused
realizers remain the *mode-F* production default as performance options — trusted and adversarially
tested, never load-bearing for the semantics. Every trusted entry's status — `kernel-v1` or
`derived(<theorem>)` — is recorded in the [runtime manifest](docs/runtime_manifest.toml) and
surfaced in the generated [TCB report](docs/tcb_report.md).

The glue between the effects — general `Match` over tagged values, the bounded `Repeat` loop, the
`Fold` list eliminator, and 16 total *checked* primitives (overflow and parse failure yield an option,
never garbage) — has its own gallery entry: [`Combinators.v`](examples/Combinators.v). On top of the
instance theorems, a shallow weakest-precondition **program logic**
([`theories/Logic.v`](theories/Logic.v), zero added trust) supports ∀-quantified specifications —
see [`theories/LogicDemo.v`](theories/LogicDemo.v).

## Quick start

Requires (verified versions): **Rocq 9.1.1, OCaml 5.4.1, dune 3.23.0, qcheck, zarith** (one opam switch).

```bash
make smoke        # day-zero gate: Rocq theory builds, extraction round-trips, OCaml 5 effects compile
make all          # the whole pipeline + every gate (this is the validation script)
make demo         # end-to-end narrated walkthrough of an "audited counter" + an HTML report
```

`make demo` is the quickest way to see the whole thesis in action: it takes one composed program
(`demo_prog` — Env + Trace + recursion + KV), shows its Rocq source and proven theorem, the idiomatic OCaml
the codegen produced, runs it under the native handlers, and confirms the proven reference agrees with the
fast OCaml (plus a codec round-trip) — printing a colorized terminal story and writing
`demo/demo_report.html`.

`make all` runs, in order, and fails loudly at the first broken link:

| target | what it does |
|--------|--------------|
| `make rocq`       | build the Rocq theories + proofs (no `Admitted`) |
| `make gen-fast`   | run `rocq-eff-codegen` → `generated/` |
| `make build-fast` | compile the generated OCaml + runtime |
| `make test`       | differential tests: reference vs fast over adversarial states |
| `make tcb-report` | regenerate [`docs/tcb_report.md`](docs/tcb_report.md) from live build facts |
| `make ci-checks`  | 6 forbidden-API / TCB gates (see below) |

A green `make all` *is* the proof that this README's workflow works — the documented commands are the test.

## What is proven vs. trusted vs. measured

This distinction is the whole point; we never blur it (see
[`kb/architecture/decisions/adr-0004-trust-model.md`](kb/architecture/decisions/adr-0004-trust-model.md)).

- **Proven** (Rocq, machine-checked, **zero axioms** — `Print Assumptions incr_correct` = *"Closed under the
  global context"*): the program meets its Hoare spec under the reference semantics, including a **frame
  clause** (other keys untouched); the monad/state laws (P7); and the spec is **non-vacuous** (an inhabitance
  lemma plus two mutants that provably fail the spec).
- **Trusted & differentially tested** (*not* proven): the OCaml compiler/runtime, the code generator, and the
  `Hashtbl` realizer. Validated by **6 programs × 5000 adversarial states = 30 000 comparisons**, with
  asserted edge-class coverage and fault injection — never asserted, always tested.
- **Measured** (*not* proven): performance and determinism, via CI gates. v1 does **not** prove cost/resource
  bounds — that is a deliberate non-goal.

## The CI gates (`make ci-checks`)

Each gate defends a specific failure mode: no `Obj.magic`; the generated code is direct-style (no free-monad
`Bind`); `Effect.perform` confined to `runtime/`; no `Admitted`/`admit`/`Axiom` (incl. `Parameter`/
`Hypothesis`/…); the committed generated file equals a fresh codegen run (no hand-edits); and the TCB report
has no undocumented drift.

## Repository layout

```
theories/     Rocq: EffIR + reference interpreter (EffIR.v), proofs (KV.v), sample programs (Samples.v)
examples/     the effects gallery: one proven, compiled demo file per effect (see examples/README.md)
extraction/   Separate Extraction of EffIR + terms -> the `ref_extracted` OCaml library
codegen/      rocq-eff-codegen: lowers the extracted EffIR ADT to direct-style OCaml
runtime/      trusted OCaml realizers (kv.ml: effect + deep handler; .mli hides the constructors)
support/      coqconv: Coq-ADT <-> zarith converters
generated/    committed codegen output (regenerated + freshness-gated)
tests/        diff_test.ml (bridge), diff_kv.ml (adversarial multi-program differential)
docs/         runtime_manifest.toml, generated tcb_report.md
ci/           the gate scripts
kb/           the knowledge base — specs, properties, decisions, runbooks (read kb/INDEX.md)
```

## Adding a program

Write a closed EffIR term in `theories/Samples.v` (fragment: `Ret`/`Bind`/`Perform`/`MatchOpt`/`Repeat`,
values via `VInt`/`VZero`/`VSucc`) and add **one line** to `Samples.all_programs` there. That single list is
the source of truth: extracting it pulls the sample as a named value, and `rocq-eff-codegen` iterates it, so
the program is extracted and code-generated to direct-style OCaml automatically — no separate codegen or
extraction list to keep in sync. (Add a differential test only if it exercises a new property.)

## Roadmap (post-slice)

**Done** (each proven axiom-free + differentially/property tested): the eight-effect family above,
composed; **bounded recursion** (`Repeat`, proven by induction) and **list elimination** (`Fold`, with
invariant rules); general **`Match`** and the 16-prim **`VPrim` registry**; a **well-formedness
checker** with a general scope-soundness theorem; the **Journal** effect with a general frame law; a
**typed binary codec pilot** with a *proven* round-trip (`theories/Codec.v`); and the **program
logic** (R14). Still open: value-shape typing (R10 phase 2), generated effect/handler modules,
abstract type realization, and (once packaged for Rocq 9.x) Mode B via MetaRocq. Built reality vs.
the fuller design is recorded in [`kb/spec/slice1-status.md`](kb/spec/slice1-status.md).

## License

BSD-3-Clause (see [`LICENSE`](LICENSE)).
</content>
