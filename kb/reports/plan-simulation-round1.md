# Plan-simulation gate — round 1 (Phase 3)

**Date:** 2026-06-20 · **Target:** `kb/plan.md` (KV vertical slice).

A fresh subagent simulated the plan against the KB and **empirically verified** the load-bearing technical
bets on the live toolchain (Rocq 9.1.1, OCaml 5.4.1, dune 3.23.0) — it ran `coqc`/`Separate Extraction` and
compiled OCaml 5 effects.

## Verified empirically (bets that held)
- `Separate Extraction` of the extrinsic first-order EffIR is **`Obj.magic`-free**. ADR-0002 premise holds.
- OCaml 5.4.1 supports both `Effect.Deep.match_with` and the `match … with effect E, k -> …` sugar.
- dune can build and extract Rocq.

## Findings that reshaped the plan
- Extraction output is **renamed and multi-module** (`coq_val`, `coq_Z`, Peano `nat`, inductive
  `string`/`ascii`; files `EffIR`, `BinNums`, `Datatypes`, …) — not one clean `eff_ir.ml`. Sync check must be
  a **`.mli` diff**, not a grep.
- dune's `coq.*` stanzas are **removed in 3.24**; the current path is `(using rocq 0.13)` with
  `(rocq.theory)` / `(rocq.extraction (prelude …) (extracted_files …) (theories … Stdlib))`, prelude excluded
  from the theory stanza, files listed explicitly.
- The interpreter's `stuck`-vs-`option` choice was **already forced** to a total `dval * state` with a
  `Dstuck` sentinel by the KB's own `verifies` definition.
- `incr` needs concrete numeric `value`; reconciled to slice-1 `key = value = Z`, `FMapAVL` over `Z_as_OT`.
- The `FMap`↔`Hashtbl` **normalizer/observable** is load-bearing and was unspecified — now a Step-1 deliverable.
- "differential green incl. T1/T6/T7" was **unmeasurable**; replaced with logged coverage counts for
  T2/T5/T6/T7. **T1 (overflow) is N/A in slice 1** (`Z` cannot overflow; no `int63` realizer yet).
- Effect arity convention pinned: tupled constructor + curried wrapper.

## Resolution
All seven blocking items resolved with the gate's proposed defaults and folded into `kb/plan.md`
("Resolutions from the plan-simulation gate") plus targeted KB fixes (runbook dune lang, reference-semantics
`Dstuck`, effect-signatures slice-1 types, ext-rocq-extraction multi-module note, edge-cases T1/coverage).

## Verdict (gate)
Executable as written **after** the seven resolutions; risk-ordering correct in spirit (integration ->
proof -> hardening), with Step 1 **re-aimed** at the real risks (normalizer + extraction wiring + multi-module
mirror) rather than the already-settled cast question. No full plan-premortem run: the slice is small,
reversible, and internal (not an irreversible data shape / public API / multi-week slice), and its central
architectural risk was already covered by the idea premortem and is Step 1's named unknown.
</content>
