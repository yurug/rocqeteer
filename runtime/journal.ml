(** Runtime Journal realizer: the OCaml backend for the [OJournal] effect (R9, adr-0013).

    [OJournal v] appends [(now_ms, v)] to a per-run buffer the handler holds — stored
    newest-first; [contents] reverses to chronological order (the trace.ml pattern; the
    reference [world.journal] is newest-first too and reversed by [observe_full]). The
    TIMESTAMP is read from the SAME injectable time source instance as the Time and
    Store handlers — construct the stack through
    [Runtime.with_store_time_and_journal] (assumption Runtime_SingleTimeSource_refines);
    a test source is stepped only BETWEEN runs, so every entry of one run carries the
    run's single instant, matching the reference's immutable [world.now_ms].

    An optional per-entry SINK callback is invoked after the buffer append (unit if
    absent): the consumer's shell decides file format, batching, fsync policy. PROVEN
    claims stop at "the buffer equals the reference journal" (differentially tested by
    diff_journal, sink==buffer included); everything sink-onward (disk bytes, crash
    atomicity, fsync) is named consumer trust — docs/runtime_manifest.toml, assumption
    Runtime_Journal_refines (adr-0013 §Decision 4). No rocqeteer text may claim journal
    durability.

    [append] returns [Rval.Unit] (the reference OJournal yields DUnit), so generated
    code can bind the result like any other op. *)

type entry = Z.t * Rval.t

type _ Effect.t += Append : Rval.t -> unit Effect.t

(** The curried public wrapper — what generated code calls for [OJournal]. *)
let append (v : Rval.t) : Rval.t =
  Effect.perform (Append v);
  Rval.Unit

(** Deep handler: each [Append] pairs the payload with a fresh read of [source]
    (one instant per run under the test protocol), pushes it newest-first onto [buf],
    then feeds the entry to [sink] if one is given. One-shot continue. *)
let run ?(sink : (entry -> unit) option) (source : Time.source)
    (buf : entry list ref) (f : unit -> 'a) : 'a =
  match f () with
  | v -> v
  | effect Append x, k ->
      let e = (source (), x) in
      buf := e :: !buf;
      (match sink with None -> () | Some s -> s e);
      Effect.Deep.continue k ()

(** Chronological view of the buffer (the reference observe_full convention). *)
let contents (buf : entry list ref) : entry list = List.rev !buf
