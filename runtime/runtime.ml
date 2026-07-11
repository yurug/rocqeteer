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
