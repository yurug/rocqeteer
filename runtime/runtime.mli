(** THE composition point for Time + Store (adr-0011 §Decision 4): one [Time.source]
    instance drives BOTH handlers, Time outermost. See docs/runtime_manifest.toml,
    assumption Runtime_SingleTimeSource_refines. *)

val with_store_and_time :
  source:Time.source -> Kv.entry Kv.T.t -> (unit -> 'a) -> 'a

val with_store_and_time_checked :
  source:Time.source -> Kv.entry Kv.T.t -> (unit -> 'a) -> ('a, Kv.error) result
