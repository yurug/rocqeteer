(** Time realizer: injectable-source clock for the [ONow] effect (R5, adr-0011).

    The effect constructor is deliberately NOT exported: clients (and generated code)
    call [now], never [Effect.perform] directly. A [source] is `unit -> Z.t`
    (milliseconds); the store realizer must share the SAME source instance — use
    [Runtime.with_store_and_time] (assumption Runtime_SingleTimeSource_refines). *)

type source = unit -> Z.t

(** The only way to read the clock from generated code; returns [Rval.Int now_ms]. *)
val now : unit -> Rval.t

(** Deep handler installing the clock source around [f]. *)
val run : source -> (unit -> 'a) -> 'a

(** Production default source: wall clock in milliseconds (Unix.gettimeofday * 1000,
    truncated). Tests inject their own virtual source instead. *)
val wall_clock_ms : source
