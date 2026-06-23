(** Trace realizer: append-only event log for the [OTrace] effect (kb/spec/effect-signatures.md). *)
val emit : Z.t -> unit
val run : Z.t list ref -> (unit -> 'a) -> 'a
val contents : Z.t list ref -> Z.t list
