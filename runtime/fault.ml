(** Fault-injection helper: performs an effect that no realizer handles, so a checked
    entrypoint must convert it to a typed error rather than crash (edge case T8). Kept in
    runtime/ so [Effect.perform] stays confined there (kb/spec/error-taxonomy.md). *)

type _ Effect.t += Unregistered : unit Effect.t

let perform_unregistered () : unit = Effect.perform Unregistered
