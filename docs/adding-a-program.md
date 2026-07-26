# Adding a program

Write a closed EffIR term in [`theories/Samples.v`](../theories/Samples.v), using the
fragment `Ret`, `Bind`, `Perform`, `Match`, `Repeat`, `Fold`, and `Prim`, with values built
from `VInt`, `VZero`, and `VSucc`.

Then add **one line** to `Samples.all_programs` in the same file.

That single list is the source of truth. Extraction pulls the sample out as a named value,
and the code generator iterates the list, so your program is extracted and code-generated to
direct-style OCaml automatically. There is no separate codegen or extraction list to keep in
sync, which is the point: a program that is proven but not generated, or generated but not
proven, should not be expressible.

Prove your Hoare specification against the reference interpreter in the theory file that
fits the effect family you are using. Every correctness theorem is expected to ship with an
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
