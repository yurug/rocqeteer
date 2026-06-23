(** Cache realizer: observationally-invisible memo store for [OCacheGet]/[OCachePut]
    (kb/spec/effect-signatures.md). *)

module T : Hashtbl.S with type key = Z.t

val get : Z.t -> Z.t option
val put : Z.t -> Z.t -> unit
val run : Z.t T.t -> (unit -> 'a) -> 'a
