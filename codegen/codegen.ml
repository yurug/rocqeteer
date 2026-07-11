(* rocqeteer-codegen — the thin CLI driver (R10 v1 split, adr-0014-wf-checker): all
   emission logic and the wf gate live in the rocqeteer.codegen LIBRARY (emit.ml/.mli);
   this executable only iterates rocqeteer's own single-source program list
   [Samples.all_programs] (defined in Rocq, extracted) onto stdout. generated/dune
   promotes the output into the source tree; ci/check_generated_fresh.sh keeps it
   honest. A wf-gate rejection has already printed the loud message to stderr — exit
   nonzero so the whole build fails (adr-0014 §4, no opt-out). *)
let () =
  try
    Rocqeteer_codegen.Emit.emit_programs Format.std_formatter
      Ref_extracted.Samples.all_programs
  with Rocqeteer_codegen.Emit.Codegen_error _ -> exit 1
