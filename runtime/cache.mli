(** Cache realizer: observationally-invisible memo store for [OCacheGet]/[OCachePut]
    (kb/spec/effect-signatures.md).

    Cache values are now [Rval.t] to match the dval universe in theories/EffIR.v
    (the reference [cache] field is [M.t dval]).  Cache keys stay [Z.t].

    [get] returns [Rval.t] (not [Rval.t option]): absent keys become [Rval.None] and
    present keys become [Rval.Some v], mirroring [opt_to_dval] in the reference semantics. *)

module T : Hashtbl.S with type key = Z.t

val get : Z.t -> Rval.t
val put : Z.t -> Rval.t -> unit
val run : Rval.t T.t -> (unit -> 'a) -> 'a
