(** Env realizer: read-only context for the [OAsk] effect (kb/spec/effect-signatures.md).

    The context type is now [Rval.t] to match the dval universe in theories/EffIR.v
    (the reference [ctx] field of [world] is already typed as [dval]). *)

type ctx = Rval.t

val ask : unit -> ctx
val run : ctx -> (unit -> 'a) -> 'a
