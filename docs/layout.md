# Repository layout

```
theories/     Rocq: EffIR and the reference interpreter (EffIR.v), the effect theories and
              their proofs, the sample programs (Samples.v), the program logic (Logic.v),
              the elaborations (Elab.v, ElabNs.v), and the concurrency layer
              (Cek.v, Sched.v, SchedHttp.v)
examples/     The effects gallery: one proven, compiled demonstration per effect family
              (dune build examples/)
extraction/   Separate extraction of EffIR and the terms into the ref_extracted library
codegen/      rocq-eff-codegen: lowers the extracted EffIR to direct-style OCaml
runtime/      The trusted OCaml realizers: effects and deep handlers, with .mli files
              hiding the constructors
support/      coqconv: converters between Rocq ADTs and zarith
generated/    Committed codegen output, regenerated and freshness-gated
tools/        The proven UNIX-sized tools: rwc and rhttpd (dune build tools/)
demo/         The narrated walkthrough behind make demo
tests/        The differential and property suites
docs/         This directory: the manifest, the generated TCB report, and these notes
ci/           The gate scripts
kb/           The knowledge base: specifications, properties, decisions, runbooks
```

Start at [`kb/INDEX.md`](../kb/INDEX.md) for the design rationale, the architecture
decisions, and the premortem that shaped them.
