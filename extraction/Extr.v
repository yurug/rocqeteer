From Stdlib Require Import Extraction.
From Rocqeteer Require Import EffIR Samples.
Extraction Language OCaml.
Separate Extraction
  EffIR.prog0 EffIR.observe EffIR.run
  Samples.sample_delete Samples.sample_two Samples.sample_ret
  Samples.sample_neg Samples.sample_nested.
