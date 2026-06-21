(** Fault injection: performs an effect no realizer handles, so a checked entrypoint must
    convert it to a typed error rather than crash (edge case T8). *)
val perform_unregistered : unit -> unit
