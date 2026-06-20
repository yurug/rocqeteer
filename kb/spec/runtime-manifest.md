---
id: runtime-manifest
type: spec
summary: The runtime manifest is the machine-readable registry mapping every Rocq realizer and refinement axiom to an OCaml symbol with purity, contract, tests, and owner; it is the audit surface of the runtime TCB.
domain: spec
last-updated: 2026-06-20
depends-on: [codegen, adr-0004-trust-model]
refines: []
related: [error-taxonomy, conv-testing-strategy, runbook-audit-checklist]
---
# Spec — Runtime manifest

## One-liner
Nothing crosses from Rocq into OCaml-land untracked: every realizer (pure prim, native data op, effect
handler) and every refinement axiom has a manifest entry with a contract, tests, and an owner. The manifest
is what the TCB report is built from.

## Scope
The manifest entry schema, the realizer classes, and the rules that make an entry valid. Replaces the
report's informal `Extract Constant` strings ([[error-taxonomy]] forbids unregistered ones).

## Entry schema (TOML, machine-readable)
```toml
[primitive."value_succ"]
ocaml_symbol = "Runtime_value.succ"
purity       = "pure"          # pure | local_mut | effectful
raises       = []
pre          = "true"
post         = "result = Z.succ x  (reference model)"
tests        = ["value_succ_matches_reference"]
owner        = "yann"

[axiom."Runtime_KV_refines"]
statement   = "forall p s, observable (run_fast_KV p s) = run_spec_KV p s"
ocaml_module = "Runtime_kv"
validated_by = ["diff_kv_incr", "diff_kv_random_adversarial"]
review_label = "tcb-axiom"
owner        = "yann"
```

## Realizer classes (report §8.2)
- **Pure native value realizers** — `value_succ`, `Z`↔`int63` (opt-in, bounded), `bytes` ops.
- **Local mutable realizers** — arrays/buffers/memo tables behind an ST-like region (pure at the boundary).
- **Effect realizers** — `ErrorE`→exceptions, `TraceE`→buffer, `CacheE`→`Hashtbl`, KV→`Hashtbl`.
- **Typed witness realizers** — GADT type witnesses / typed encodings (Phase 4; the only place a reviewed `Obj.magic` may live).

## Validity rules (CI-enforced)
1. Every `VPrim`/`Perform` op named in generated code resolves to a manifest entry, else codegen fails.
2. Every `axiom.*` entry appears in `tcb_report.md`; a new axiom without `review_label` fails CI ([[adr-0004-trust-model]]).
3. Every entry has ≥1 test and an owner ("every runtime primitive must have an owner" — report maxim 10).
4. `purity = "pure"` realizers must have a faithful Rocq reference model used by the differential oracle.
5. `int63`/bounded realizers must declare a *proven or dynamically-checked* bound (no silent wraparound — C4).

## Agent notes
> The manifest is the contract between the proven world and the trusted world. When you add a realizer you
> are *expanding the TCB*; the entry (purity + pre/post + tests + owner) is the price. Treat a missing
> entry as a hard error, never a TODO.

## Related files
- `spec/codegen.md` — resolves prim/op names against this manifest.
- `runbooks/audit-checklist.md` — the per-build review of new/changed manifest entries.
- `conventions/testing-strategy.md` — the tests every entry must carry.
</content>
