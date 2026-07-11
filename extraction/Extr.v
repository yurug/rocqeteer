From Stdlib Require Import Extraction.
From Rocqeteer Require Import EffIR Samples Wf.
Extraction Language OCaml.
(* all_programs is the single source of truth: extracting it pulls every referenced sample
   as a named value (so the tests can still use Samples.sample_X), and the codegen iterates
   it. Plus the EffIR entry points the differential tests call, and the R10 v1 PROVEN
   well-formedness checker Wf.wf_tm (adr-0014): the codegen gate runs the EXTRACTED
   checker on every program pre-emission — one implementation, two uses. *)
Separate Extraction
  Samples.all_programs
  EffIR.prog0 EffIR.observe EffIR.observe_full EffIR.run
  Wf.wf_tm Wf.wf_val Wf.op_arity Wf.prim_arity Wf.pat_binders.
