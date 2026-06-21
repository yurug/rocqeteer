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
```

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

Write a closed EffIR term in `theories/Samples.v` (slice-1 fragment: `Ret`/`Bind`/`Perform`/`MatchOpt`,
values via `VInt`/`VZero`/`VSucc`), add it to the `Separate Extraction` list in `extraction/Extr.v`, the
`programs` list in `codegen/codegen.ml`, and the `programs` list in `tests/diff_kv.ml`. It is then extracted,
code-generated to direct-style OCaml, and differentially tested automatically. (Generating these lists is on
the breadth roadmap.)

## Roadmap (post-slice)

The **`Error` effect** (`OThrow` + a native-exception backend, with the `throw e;;k = throw e` law proven
and an outcome+state differential test) is **done** — the first breadth iteration. Next: `Env`/`Trace`/`Cache`,
recursion, GADT witnesses, and a `data-encoding`-style verified binary codec pilot. The boundaries between
built reality and the fuller design are recorded in [`kb/spec/slice1-status.md`](kb/spec/slice1-status.md).

## License

MIT (see source headers).
</content>
