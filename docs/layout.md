# Repository layout

```
theories/     The INSTALLED generic library: EffIR and the reference interpreter (EffIR.v,
              including the generic file/socket/concurrency ops), the effect theories and
              their proofs, the generic sample programs (Samples.v), the program logic
              (Logic.v), the elaborations (Elab.v, ElabNs.v), and the concurrency machine
              + scheduler (Cek.v, Sched.v). Domain-independent — no application lives here.
apps/         Applications built WITH the library, NOT installed (RocqeteerApps): the
              application programs (AppSamples.v) and their proofs — wc (FileIO.v), the
              HTTP/1.0 server (SockIO.v), the concurrent HTTP driver (SchedHttp.v).
              AppSamples also holds the codegen's combined program list.
examples/     The effects gallery: one proven, compiled demonstration per effect family
              (dune build examples/)
extraction/   Separate extraction of EffIR and the terms into the ref_extracted library
codegen/      rocq-eff-codegen: lowers the extracted EffIR to direct-style OCaml
runtime/      The trusted OCaml realizers: effects and deep handlers, with .mli files
              hiding the constructors
support/      coqconv: converters between Rocq ADTs and zarith
generated/    Committed codegen output, regenerated and freshness-gated
tools/        The proven UNIX-sized tools: rwc, rhttpd, rhttpd_conc (dune build tools/)
demo/         The narrated walkthrough behind make demo
tests/        The differential and property suites
docs/         This directory: the manifest, the generated TCB report, and these notes
ci/           The gate scripts
kb/           The knowledge base: specifications, properties, decisions, runbooks
```

Start at [`kb/INDEX.md`](../kb/INDEX.md) for the design rationale, the architecture
decisions, and the premortem that shaped them.
