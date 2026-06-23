From Stdlib Require Import Extraction.
From Rocqeteer Require Import EffIR Samples.
Extraction Language OCaml.
Separate Extraction
  EffIR.prog0 EffIR.observe EffIR.observe_full EffIR.run
  Samples.sample_delete Samples.sample_two Samples.sample_ret
  Samples.sample_neg Samples.sample_nested
  Samples.sample_throw Samples.sample_guard5
  Samples.sample_env Samples.sample_trace.
