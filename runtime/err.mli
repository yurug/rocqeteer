(** Error realizer: native-exception backend for the [OThrow] effect
    (kb/conventions/error-handling.md).

    Error values are now [Rval.t] to match the dval universe in theories/EffIR.v
    (the reference [OErr] carries a [dval]). *)

(** Abort the computation with error value [e]. *)
val throw : Rval.t -> 'a

(** Run [f], turning a [throw] into [Error e]; other exceptions propagate. *)
val run_error : (unit -> 'a) -> ('a, Rval.t) result
