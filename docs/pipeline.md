# The build pipeline and its gates

## Targets

| Target | What it does |
|---|---|
| `make smoke` | Day-zero gate: `dune build theories/ extraction/ runtime/` |
| `make rocq` | Build the Rocq theories and proofs |
| `make gen-fast` | Run the code generator into `generated/` (a dune rule in promote mode) |
| `make build-fast` | Compile the generated OCaml, the runtime, the codegen, and support |
| `make test` | `dune test`: the differential and property suites |
| `make tcb-report` | Regenerate [`tcb_report.md`](tcb_report.md) from live build facts |
| `make ci-checks` | The eight gates below |
| `make kb-lint` | Knowledge base frontmatter, link, and orphan lint |
| `make demo` | The narrated end-to-end walkthrough, plus `demo/demo_report.html` |
| `make all` | `smoke rocq gen-fast build-fast test tcb-report ci-checks` |

Two things `make all` does not build: the effects gallery under `examples/`, and the proven
tools under `tools/`. Build them explicitly with `dune build examples/` and
`dune build tools/`.

## The eight gates

Each gate defends one failure mode, and `make ci-checks` fails loudly at the first one that
trips.

| Script | Gate |
|---|---|
| `ci/check_no_objmagic.sh` | No `Obj.magic`, in extracted or hand-written sources |
| `ci/check_no_bind_in_generated.sh` | The generated code is direct-style: no free-monad `Bind` (property P3) |
| `ci/check_no_stray_perform.sh` | `Effect.perform` stays confined to `runtime/` |
| `ci/check_no_admitted.sh` | No `Admitted`, `admit`, `Axiom`, `Parameter`, `Hypothesis`, `Conjecture`, or `Variable` in `theories/` |
| `ci/check_generated_fresh.sh` | The committed generated file equals a fresh codegen run, so hand-edits cannot survive |
| `ci/check_discharge.sh` | Every manifest effect names `kernel-v1` or `derived(<theorem>)`, and that theorem exists |
| `ci/check_tcb.sh` | Regenerate the report, assert the invariants, fail on silent TCB drift (the toolchain block is informational and excluded from the comparison, so a different Rocq or OCaml point release is not a failure) |
| `ci/check_kb_lint.sh` | Knowledge base lint |

Note that `check_no_admitted.sh` is scoped to `theories/`. The gallery under `examples/`
carries its own proofs and is not covered by that gate.

There is no hosted CI service configured for this repository; the gates run locally through
`make ci-checks`.
