From Stdlib Require Import Extraction.
From Rocqeteer Require Import EffIR Samples.
Extraction Language OCaml.
(* all_programs is the single source of truth: extracting it pulls every referenced sample
   as a named value (so the tests can still use Samples.sample_X), and the codegen iterates
   it. Plus the EffIR entry points the differential tests call. *)
Separate Extraction
  Samples.all_programs
  EffIR.prog0 EffIR.observe EffIR.observe_full EffIR.run.
