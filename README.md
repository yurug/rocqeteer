# Rocqeteer

**Use Rocq as a certified programming language: write effectful programs in Rocq, *prove* them against
reference semantics, and *run* them as fast, idiomatic OCaml 5 — with a small, explicit, auditable trust
base.**

Rocqeteer is a domain-independent toolchain. Rocq owns the specifications, laws, and proofs; OCaml owns the
runtime — native data, effect handlers, direct-style execution. One first-order intermediate representation
(**EffIR**) is shared by the Rocq reference interpreter and the OCaml code generator, so *the program you
prove and the program you run cannot silently become different programs*.

> **Status:** the **KV vertical slice** (a key-value state effect) is complete end-to-end and verified.
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

**Done so far** (each proven axiom-free + differentially/property tested): the five-effect MVP family —
**State, Error, Env, Trace, Cache** — composed; **bounded recursion** (`Repeat`, proven by induction); and a
**typed binary codec pilot** with a *proven* round-trip (`theories/Codec.v`) and a GADT/`bytes` realizer with
no unsafe casts. Still open: general `Match`/`VPrim` + an IR typechecker, generated effect/handler modules,
abstract type realization, and (once packaged for Rocq 9.x) Mode B via MetaRocq. Built reality vs. the fuller
design is recorded in [`kb/spec/slice1-status.md`](kb/spec/slice1-status.md).

## License

MIT (see source headers).
</content>
