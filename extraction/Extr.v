From Stdlib Require Import Extraction.
From Rocqeteer Require Import EffIR Samples Wf Elab.
Extraction Language OCaml.
(* all_programs is the single source of truth: extracting it pulls every referenced sample
   as a named value (so the tests can still use Samples.sample_X), and the codegen iterates
   it. Plus the EffIR entry points the differential tests call, and the R10 v1 PROVEN
   well-formedness checker Wf.wf_tm (adr-0014): the codegen gate runs the EXTRACTED
   checker on every program pre-emission — one implementation, two uses.
   ADR-0016 mode K: the PROVEN Expiry elaboration Elab.elab (theories/Elab.v,
   elab_simulates) and the pre-elaborated twin list Elab.elab_programs — the codegen
   emits it into generated/progk_generated.ml, which runs against KERNEL realizers
   only (Kv.run_kernel: no deadline logic, no clock). *)
Separate Extraction
  Samples.all_programs
  Elab.elab Elab.elab_programs
  EffIR.prog0 EffIR.observe EffIR.observe_full EffIR.run
  Wf.wf_tm Wf.wf_val Wf.op_arity Wf.prim_arity Wf.pat_binders.
