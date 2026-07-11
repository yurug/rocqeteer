(** THE composition point for Time + Store (adr-0011 §Decision 4).

    Both handlers are constructed from ONE [Time.source] instance, with Time OUTERMOST —
    the store realizer reads the shared source directly, and any [ONow] performed by the
    program escapes the store handler to the Time handler outside it. This single-source
    discipline is the named trust assumption [Runtime_SingleTimeSource_refines] in
    docs/runtime_manifest.toml: store-now ≡ time-now; a test source is stepped only
    BETWEEN runs, so reference (one immutable [now_ms]) and fast (per-op source reads)
    see the same instant per run. *)

(** Run [f] under Time(source) ∘ Store(table, same source). *)
let with_store_and_time ~(source : Time.source) (table : Kv.entry Kv.T.t)
    (f : unit -> 'a) : 'a =
  Time.run source (fun () -> Kv.run ~now:source table f)

(** Checked variant: unhandled effects / stray exceptions become typed errors (T8). *)
let with_store_and_time_checked ~(source : Time.source) (table : Kv.entry Kv.T.t)
    (f : unit -> 'a) : ('a, Kv.error) result =
  Time.run source (fun () -> Kv.run_checked ~now:source table f)

(** R9 (adr-0013): Time(source) ∘ Journal(source, jbuf, ?sink) ∘ Store(table, source) —
    the ONE source instance drives all three handlers (Journal is a state-carrying
    handler anywhere inside Time's scope, adr-0013 §Decision 5; like the store it reads
    the shared source directly). The journal-free entrypoints above stay as-is for the
    existing callers. Everything sink-onward is consumer trust
    (Runtime_Journal_refines). *)
let with_store_time_and_journal ?sink ~(source : Time.source)
    (table : Kv.entry Kv.T.t) (jbuf : Journal.entry list ref)
    (f : unit -> 'a) : 'a =
  Time.run source (fun () ->
      Journal.run ?sink source jbuf (fun () -> Kv.run ~now:source table f))
