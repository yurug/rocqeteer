---
id: ext-rocq-extraction
type: external
summary: Rocq 9.1's extraction plugin erases logical content and prints fairly direct ML; it copies Extract Constant code as unchecked strings, may insert Obj.magic (no GADTs generated), and does not improve algorithmic complexity — constraints that shape ADR-0002/0003/0004.
domain: external
last-updated: 2026-06-20
depends-on: []
refines: []
related: [adr-0002-extraction-bridge, adr-0003-dependency-budget, adr-0004-trust-model, codegen]
---
# External — Rocq extraction (plugin `coq-core.plugins.extraction`, Rocq 9.1.1)

## One-liner
We use extraction for exactly two things: (1) emit the **EffIR datatype + example terms** as an OCaml ADT
for the codegen to consume ([[adr-0002-extraction-bridge]]); (2) build the **reference interpreter** as a
runnable (slow, faithful) OCaml executable for differential testing. We do **not** rely on it to optimize.

## Actual runtime behavior & constraints (report §3.1–3.3, R1–R3)
- **Erases logical content; prints direct ML.** Extracted shape follows the Gallina definition, not a
  runtime-tuned one. It is *not* an optimizing compiler.
- **No complexity magic.** Mapping `nat`→`int` does **not** change asymptotics of `Nat.mul` etc.; efficient
  realizers must be supplied. The historic `ExtrOcamlNatInt` realizers are explicitly *uncertified*
  (testing/prototyping only). ⇒ we do **not** globally remap `nat`; use `Z` (zarith) for values (C4).
- **`Extract Constant` code is copied as an unchecked string** — extraction does not verify its ML type. ⇒
  forbidden unless it goes through the runtime manifest ([[runtime-manifest]]); unregistered ones fail CI.
- **`Obj.magic` insertion.** Extraction may insert `Obj.magic` where Rocq and ML types diverge, and does
  **not** generate GADTs for those cases. ⇒ keep EffIR's *extracted shape* free of dependent indices that
  would force casts; type indices stay proof-side (see [[effir]] "no dependent matches that need casts").
- **Primitive realizers must be user-supplied.** `ExtrOCamlInt63`/`Floats`/`PArray`/`PString` map Rocq
  primitives to OCaml, but the OCaml modules themselves are not produced by extraction — they are our `runtime/`.

## "Request budget" analogue
Extraction is a build-time, one-shot operation (no API rate limit). The risk is not call volume but
**faithfulness of the extracted shape**: we mitigate by (a) extracting a *simple first-order datatype*, and
(b) a CI check that the extracted EffIR `.mli` matches the hand-written `codegen/eff_ir.ml` mirror.

## How we configure it
- A `theories/Extraction/*.v` with `Extraction Language OCaml`, `Extract Inductive`/`Extract Constant` only
  for **manifest-registered** realizers (slice 1: `Z -> Zarith.Z.t`), and `Separate Extraction` of the EffIR
  datatype + example terms + the reference `run`.
- Dune wiring: `(using rocq 0.13)` with a `(rocq.extraction (prelude …) (extracted_files …) (theories …
  Stdlib))` stanza (prelude `.v` excluded from any theory stanza; every extracted `.ml/.mli` listed). The
  legacy `coq.*` stanzas are removed in dune 3.24.
- **Verified shape:** extraction is `Obj.magic`-free but **renamed and multi-module** — `val -> coq_val`,
  `Z -> coq_Z`, Peano `nat`, inductive `string`/`ascii`, across files `EffIR`/`BinNums`/`Datatypes`/…. The
  `codegen/eff_ir.ml` mirror reflects that real shape, and the sync check is a **`.mli` diff**, not a grep.
- `Print Assumptions <thm>` output is captured into `tcb_report.md` for every example theorem.

## Agent notes
> Two failure traps from the premortem live here: (1) trusting an `Extract Constant` string — never, it is
> unchecked; (2) letting extraction sprinkle `Obj.magic` — keep the extracted datatype non-dependent so it
> can't. If extraction emits an `Obj.magic`, treat it as a design bug in the EffIR shape, not as acceptable.

## Related files
- `architecture/decisions/adr-0002-extraction-bridge.md` — why we extract the ADT instead of printing JSON.
- `spec/runtime-manifest.md` — the only sanctioned home for `Extract Constant`/realizers.
</content>
