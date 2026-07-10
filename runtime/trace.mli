(** Trace realizer: append-only event log for the [OTrace] effect (kb/spec/effect-signatures.md).

    Event type is now [Rval.t] to match the dval universe in theories/EffIR.v
    (the reference [trace] field of [world] is [list dval]). *)

val emit : Rval.t -> unit
val run : Rval.t list ref -> (unit -> 'a) -> 'a
val contents : Rval.t list ref -> Rval.t list
