From Stdlib Require Import Extraction.
From Rocqeteer Require Import EffIR Samples Wf Elab ElabNs Sched.
From RocqeteerApps Require Import AppSamples.
Extraction Language OCaml.
(* all_programs is the single source of truth: extracting it pulls every referenced sample
   as a named value (so the tests can still use Samples.sample_X), and the codegen iterates
   it. Plus the EffIR entry points the differential tests call, and the R10 v1 PROVEN
   well-formedness checker Wf.wf_tm (adr-0014): the codegen gate runs the EXTRACTED
   checker on every program pre-emission — one implementation, two uses.
   ADR-0016 mode K: the PROVEN tower layers — Expiry (Elab.elab, elab_simulates)
   and the consolidation (ElabNs.elab_ns; cache/journal into the escaped store) —
   plus the COMPOSED list ElabNs.elab_full_programs (elab_full_simulates), which the
   codegen emits into generated/progk_generated.ml: it runs against KERNEL realizers
   only (Kv.run_kernel: no deadline logic, no clock, no cache/journal realizers). *)
Separate Extraction
  (* The codegen's source-of-truth is the COMBINED list (generic Samples.all_programs ++
     the applications), defined in RocqeteerApps.AppSamples so the installed theories/
     library carries no application programs.  Extracting it pulls every referenced
     sample as a named value (generic ones into Samples.ml, applications into
     AppSamples.ml).  The two proven tower elaborations over the same list drive mode-K. *)
  AppSamples.all_programs_full AppSamples.elab_programs_full AppSamples.elab_full_programs_full
  Elab.elab ElabNs.elab_ns ElabNs.elab_full
  EffIR.prog0 EffIR.observe EffIR.observe_full EffIR.run
  EffIR.run_file EffIR.observe_file EffIR.run_sock EffIR.observe_sock
  Wf.wf_tm Wf.wf_val Wf.op_arity Wf.prim_arity Wf.pat_binders
  (* C5 (adr-0019): the reference scheduler + its proven sample states, for the
     runtime differential (tests/diff_sched.ml runs the OCaml Sched realizer against
     these and asserts equal observables). *)
  Sched.run_sched Sched.sresult_of Sched.swld Sched.sfib Sched.sdone
  Sched.nb Sched.bodies_sp Sched.s_int Sched.s_pc Sched.s_dead Sched.s_sp.
