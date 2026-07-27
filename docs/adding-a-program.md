# Adding a program

Write a closed EffIR term using the fragment `Ret`, `Bind`, `Perform`, `Match`, `Repeat`,
`Fold`, and `Prim`, with values built from `VInt`, `VZero`, and `VSucc`. Where it goes
depends on what it is:

- A **generic demonstration** program → [`theories/Samples.v`](../theories/Samples.v); add
  one line to `Samples.all_programs`.
- An **application** program (something domain-specific, like a server) →
  [`apps/AppSamples.v`](../apps/AppSamples.v); add one line to `app_programs`. This keeps the
  installed `theories/` library domain-independent.

`AppSamples.all_programs_full` is `Samples.all_programs ++ app_programs` — the single source
of truth the codegen consumes. Extraction pulls the sample out as a named value, and the code
generator iterates the combined list, so your program is extracted and code-generated to
direct-style OCaml automatically. There is no separate codegen or extraction list to keep in
sync, which is the point: a program that is proven but not generated, or generated but not
proven, should not be expressible.

Prove your Hoare specification against the reference interpreter in the theory file that
fits the effect family you are using — a generic-effect theory in `theories/`, or an
application-proof theory in `apps/`. Every correctness theorem is expected to ship with an
inhabitance lemma and a mutant that provably fails the specification, so that a vacuous
specification cannot pass unnoticed.

Add a differential test only if your program exercises a property the existing suites do not
already cover.

Then:

```bash
make gen-fast build-fast test tcb-report ci-checks
```

The freshness gate will fail if the committed generated file no longer matches what the
generator produces, which is how hand-edits to generated code are caught.
