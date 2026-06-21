(** Error realizer: native-exception backend for the [OThrow] effect (kb/conventions/error-handling.md). *)

(** Abort the computation with error value [e]. *)
val throw : Z.t -> 'a

(** Run [f], turning a [throw] into [Error e]; other exceptions propagate. *)
val run_error : (unit -> 'a) -> ('a, Z.t) result
