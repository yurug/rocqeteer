(** Env realizer: read-only context for the [OAsk] effect (kb/spec/effect-signatures.md). *)
type ctx = Z.t
val ask : unit -> ctx
val run : ctx -> (unit -> 'a) -> 'a
