(** Journal realizer: append-only (timestamp, value) log for the [OJournal] effect
    (R9, adr-0013-journal-effect).

    The effect constructor is deliberately NOT exported: clients (and generated code)
    call [append], never [Effect.perform] directly. Timestamps come from a
    [Time.source] that MUST be the same instance as the Time/Store handlers' — use
    [Runtime.with_store_time_and_journal] (assumption Runtime_SingleTimeSource_refines).
    The optional [sink] is called once per entry AFTER the buffer append; everything
    sink-onward (disk bytes, crash atomicity, fsync) is named consumer trust
    (assumption Runtime_Journal_refines) — durability is NOT proven. *)

type entry = Z.t * Rval.t

(** The only way to journal from generated code; returns [Rval.Unit] (reference DUnit). *)
val append : Rval.t -> Rval.t

(** Deep handler installing the journal interpretation around [f]: buffer newest-first,
    per-entry timestamp from [source], optional per-entry [sink] callback. *)
val run : ?sink:(entry -> unit) -> Time.source -> entry list ref -> (unit -> 'a) -> 'a

(** Chronological view of the buffer (oldest first), like the reference observe_full. *)
val contents : entry list ref -> entry list
