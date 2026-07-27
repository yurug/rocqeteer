# Rocqeteer

**Use Rocq as a certified programming language: write effectful programs in Rocq, *prove*
them against reference semantics, and *run* them as fast, idiomatic OCaml 5, with a small,
explicit, auditable trust base.**

Rocq owns the specifications, the laws, and the proofs. OCaml owns the runtime: native data,
effect handlers, direct-style execution. One first-order intermediate representation
(**EffIR**) is shared by the Rocq reference interpreter and the OCaml code generator, so the
program you prove and the program you run cannot silently become different programs.

Two proven UNIX-sized tools ship with it: `rwc`, a byte-counting `wc`, and `rhttpd`, a
one-shot HTTP/1.0 server. Its first real consumer is redoq, a Redis-compatible server whose
data commands, RESP codecs, and append-only-file recovery are proven with exactly these
tools.

## What it does

You write an effectful program in Rocq as an EffIR term, you prove a Hoare specification
about it against a pure reference interpreter, and one command does the rest:

1. **extracts** the reference interpreter to OCaml, the slow and faithful oracle, then
2. **generates** idiomatic direct-style OCaml 5 for the *same* term (`Effect.perform`, deep
   handlers, native data structures, no monad interpreter), then
3. **differentially tests** the two against each other on thousands of adversarial inputs,
   and
4. emits a **TCB report** naming every trust assumption that remains.

```
Rocq EffIR term ──extract──▶ reference interpreter ─┐
       │                                            ├─▶ differential test (ref == fast?) ─▶ TCB report
       └──────codegen──────▶ direct-style OCaml ────┘
```

## Quick start

You need one opam switch with Rocq 9.1, OCaml 5.3 or later, dune 3.23, qcheck and
zarith. The exact versions of the last reference run are recorded in
[`docs/tcb_report.md`](docs/tcb_report.md), which the build regenerates.

```bash
make demo         # the whole thesis in five minutes, narrated
make smoke        # day-zero gate: theories build, extraction round-trips, effects compile
make all          # the full pipeline and every gate; this is the validation script
```

`make demo` takes one composed program, shows its Rocq source and its proven theorem, shows
the OCaml the code generator produced, runs it under the native handlers, and confirms that
the proven reference agrees with the fast path. It prints a colourised story and writes
`demo/demo_report.html`.

To run the proven tools:

```bash
dune build tools/
dune exec tools/rwc.exe -- FILE           # byte count; the proven core caps at 32 KiB
dune exec tools/rhttpd.exe -- PORT        # serves 16 one-shot connections on 127.0.0.1
```

The effects gallery is built separately, with `dune build examples/`: one proven, compiled
demonstration file per effect family, listed in [`examples/README.md`](examples/README.md).

## What is proven, what is trusted, what is measured

This distinction is the whole point, and blurring it would defeat the exercise.

**Proven**, machine-checked in Rocq with zero axioms: the program meets its Hoare
specification under the reference semantics, including the frame clause, and the
specification is non-vacuous, since every correctness theorem ships with an inhabitance
lemma and a mutant that provably fails.

**Trusted and differentially tested**, not proven: everything between the reference and the
running binary. Rocq's extraction, the code generator, the OCaml compiler and runtime, the
effect handlers, and the realizers. Each assumption is a named row in
[`docs/runtime_manifest.toml`](docs/runtime_manifest.toml), surfaced in the generated
[TCB report](docs/tcb_report.md), and backed by adversarial differential tests rather than
by assertion.

**Measured**, not proven: performance, determinism, and durability. Everything from the
journal sink onward, meaning disk bytes, fsync, and crash atomicity, is named consumer trust
and is explicitly out of scope.

Some trust does get discharged rather than assumed: the expiry, cache, and journal families
each have an axiom-free refinement theorem compiling them into kernel operations, and a gate
fails the build if the manifest names a discharge theorem that does not exist.

## Documentation

| | |
|---|---|
| [`docs/effects.md`](docs/effects.md) | The effect families, their operations, and the towers that discharge three of them |
| [`docs/pipeline.md`](docs/pipeline.md) | Every make target, and the eight gates `make ci-checks` runs |
| [`docs/adding-a-program.md`](docs/adding-a-program.md) | How to add a program and get it proven, extracted, and generated |
| [`docs/layout.md`](docs/layout.md) | Repository layout and where each concern lives |
| [`docs/tcb_report.md`](docs/tcb_report.md) | Generated from live build facts: assumptions, realizers, gate results |
| [`docs/design-report.md`](docs/design-report.md) | The original design report: trust boundaries, alternatives, rationale |
| [`kb/INDEX.md`](kb/INDEX.md) | The knowledge base: specifications, properties, decisions, runbooks |

## Status

Experimental, and honest about its edges. IR v2 is complete: ten effect families over one
explicit world, general `Match`, `Fold`, bounded `Repeat`, checked primitives that return an
option rather than garbage, a well-formedness checker, and a weakest-precondition program
logic. Proof counts and assumption counts are not repeated here on purpose, since
`make tcb-report` regenerates them from the build and the README would only rot.

A concurrency layer exists in Rocq (a CEK step machine with an adequacy theorem, a
cooperative scheduler whose determinism comes from an injected schedule, and the HTTP server
recovered under a concurrent acceptor and worker structure), but it stops at the Rocq
boundary: no runtime realizer, no code generation path, no differential test yet.

Where this fits the wider picture: rocqeteer is how the harness gets its strongest check,
formal verification of the critical modules, in the loop described in
[Keep the engineer in the loop](https://yann.regis-gianas.org/en/posts/harness-not-output/).
It was built with the spec-driven methodology in
[agentic-dev-kit](https://github.com/yurug/agentic-dev-kit).

If you try it, tell me what broke. Issues, pull requests, and a plain "this made no sense to
me" are all welcome.

## License

MIT (see [`LICENSE`](LICENSE)).
