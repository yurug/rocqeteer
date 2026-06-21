---
id: runbook-build-validate
type: procedure
summary: The end-to-end pipeline commands and CI gates — build Rocq, extract reference+EffIR, run codegen, build fast OCaml, run differential tests, generate and diff the TCB report.
domain: runbooks
last-updated: 2026-06-20
depends-on: [arch-overview, codegen, conv-testing-strategy]
refines: []
related: [runbook-audit-checklist, error-taxonomy, prop-non-functional]
---
# Runbook — build & validate (the pipeline)

## One-liner
One command sequence carries a program from Rocq proof to a green differential test, failing loudly at the
first broken link. Mirrors report §12.3 CI gates; targets are placeholders until the dune workspace exists.

## Toolchain (verified 2026-06-20)
Rocq 9.1.1 · OCaml 5.4.1 · dune 3.23.0 · qcheck 0.91 · zarith 1.14. Switch: `default` (opam). Effects sugar
`match … with effect E, k -> …` available (5.3+).

## Day-zero gate (before any other work — [[adr-0003-dependency-budget]])
```
make smoke      # (using rocq 0.13) workspace: builds a trivial Rocq file, EXTRACTS it (Separate Extraction
                # round-trip), and builds a 3-line OCaml effects program (perform/deep handler).
                # Proves deps + effects syntax + the extraction wiring work here. Block all work behind it.
```
Dune Rocq integration uses **`(using rocq 0.13)`**: `(rocq.theory …)` for libraries plus a *separate*
`(rocq.extraction (prelude …) (extracted_files …) (theories … Stdlib))` — prelude excluded from any theory
stanza, every extracted `.ml/.mli` listed explicitly. The legacy `coq.*` stanzas are removed in dune 3.24.

## Pipeline (each step gates the next)
```
make rocq           # build theories/ : EffIR, signatures, reference interpreter, laws, proofs (no Admitted)
make extract-ref    # extract the reference interpreter + EffIR datatype/terms to OCaml (slow, faithful)
make gen-fast       # run rocq-eff-codegen on the extracted EffIR -> generated/ (direct-style OCaml)
make build-fast     # dune build generated/ + runtime/  (P4: must type-check under 5.4.1)
make test           # unit + golden + differential (reference vs fast, adversarial inputs) + fault injection
make fuzz-smoke     # bounded biased fuzzing every PR (P5 / T1-T10)
make tcb-report     # regenerate tcb_report.md (versions, Print Assumptions, Obj.magic, Extract Constant, entrypoints)
make bench-smoke    # NF4 latency smoke: fail PR on >10% regression vs baseline
```

## Hard-fail conditions (CI — [[error-taxonomy]] §3)
Unregistered primitive · new `Axiom` without `tcb-axiom` label · `Obj.magic` outside the witness module ·
`Effect.perform` outside generated/runtime · unregistered `external` C decl · manually-edited generated file
(hash mismatch) · public entrypoint without a differential test · any `Admitted`/`admit` · `tcb_report.md`
diff unreviewed.

## Slice-1 definition of done (gate to "breadth allowed" — [[adr-0006-vertical-slice]])
`make rocq` (incr_spec proven + inhabitance + a failing mutant) → `make extract-ref` → `make gen-fast`
(generated `incr` is direct-style, no `Bind`) → `make build-fast` → `make test` (KV differential green on
adversarial inputs) → `make tcb-report` (lists `Runtime_KV_refines` + `value_succ`). All green & committed.

## Agent notes
> Run `make smoke` first, every session, before trusting anything else — a broken switch or missing effects
> syntax invalidates every downstream result. The pipeline is intentionally fail-fast: a red step means stop
> and fix, not skip.

## Related files
- `runbooks/audit-checklist.md` — the quality audit run after the pipeline is green.
- `spec/codegen.md` — what `gen-fast` does and the headers it stamps.
</content>
