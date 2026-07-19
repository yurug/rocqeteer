(* rocqeteer-codegen — the thin CLI driver (R10 v1 split, adr-0014-wf-checker): all
   emission logic and the wf gate live in the rocqeteer.codegen LIBRARY (emit.ml/.mli);
   this executable only iterates rocqeteer's own single-source program list
   [Samples.all_programs] (defined in Rocq, extracted) onto stdout. generated/dune
   promotes the output into the source tree; ci/check_generated_fresh.sh keeps it
   honest. A wf-gate rejection has already printed the loud message to stderr — exit
   nonzero so the whole build fails (adr-0014 §4, no opt-out).

   With [--elab] (ADR-0016 mode K) it iterates [Elab.elab_programs] instead — the
   SAME list, pre-elaborated IN ROCQ by the proven Expiry elaboration (theories/
   Elab.v, elab_simulates): no elaboration logic lives in this trusted driver. *)
let () =
  let programs =
    if Array.length Sys.argv > 1 && Sys.argv.(1) = "--elab" then
      Ref_extracted.Elab.elab_programs
    else Ref_extracted.Samples.all_programs
  in
  try Rocqeteer_codegen.Emit.emit_programs Format.std_formatter programs
  with Rocqeteer_codegen.Emit.Codegen_error _ -> exit 1
