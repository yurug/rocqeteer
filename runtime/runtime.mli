(** THE composition point for Time + Store (adr-0011 §Decision 4), extended by R9 with
    the Journal handler (adr-0013 §Decision 5): one [Time.source] instance drives ALL
    handlers, Time outermost. See docs/runtime_manifest.toml, assumptions
    Runtime_SingleTimeSource_refines and Runtime_Journal_refines. *)

val with_store_and_time :
  source:Time.source -> Kv.entry Kv.T.t -> (unit -> 'a) -> 'a

val with_store_and_time_checked :
  source:Time.source -> Kv.entry Kv.T.t -> (unit -> 'a) -> ('a, Kv.error) result

(** Time ∘ Journal(?sink) ∘ Store, one shared source; journal buffer newest-first
    (read it back chronologically via [Journal.contents]). *)
val with_store_time_and_journal :
  ?sink:(Journal.entry -> unit) ->
  source:Time.source ->
  Kv.entry Kv.T.t -> Journal.entry list ref -> (unit -> 'a) -> 'a
