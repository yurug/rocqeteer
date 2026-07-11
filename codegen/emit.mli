(** Emit — the rocqeteer codegen library API (R10 v1, adr-0014-wf-checker).

    The emission core behind the [rocqeteer-codegen] executable, exposed as the dune
    library (public_name rocqeteer.codegen) so consumers (e.g. an engine built on
    rocqeteer) can lower THEIR extracted single-source program list into their own
    generated/ file: link the library, extract [all_programs] against the installed
    [rocqeteer.extracted] types, call [emit_programs] on a formatter over that file. *)

exception Codegen_error of string
(** Out-of-fragment input (wrong effect/prim arity, out-of-scope de Bruijn index in a
    lowering position, non-bytes key, …) and wf-gate rejection fail LOUDLY with this
    exception rather than emitting unsound code (kb/spec/error-taxonomy.md). *)

val emit_programs :
  Format.formatter ->
  (Ref_extracted.String.string, Ref_extracted.EffIR.tm) Ref_extracted.Datatypes.prod
    Ref_extracted.Datatypes.list ->
  unit
(** [emit_programs fmt programs]: wf-gate every program of the extracted
    [(name, tm)] list with the EXTRACTED, PROVEN well-formedness checker [Wf.wf_tm]
    (theories/Wf.v: de Bruijn scope + op/prim arity + pattern binder counts;
    well-FORMED, not well-typed — adr-0014 §4, no opt-out, no OCaml reimplementation),
    then emit the standard generated-file header plus one direct-style
    [let <name> () = <body>] per program, in list order.

    On the FIRST ill-formed program it prints
    ["program <name>: ill-formed (wf_tm = false)"] to stderr and raises
    [Codegen_error] with the same message BEFORE any byte is written to [fmt] — the
    CLI driver therefore exits nonzero and the whole run fails. *)
