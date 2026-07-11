(** Cache realizer: observationally-invisible memo store for [OCacheGet]/[OCachePut]
    (kb/spec/effect-signatures.md).

    Cache values are [Rval.t] to match the dval universe in theories/EffIR.v (the
    reference [cache] field is [M.t dval]). Cache keys are native [bytes] since R4
    (adr-0011); the cache carries NO deadlines.

    [get] returns [Rval.t] (not [Rval.t option]): absent keys become [Rval.None] and
    present keys become [Rval.Some v], mirroring [opt_to_dval] in the reference semantics. *)

module T : Hashtbl.S with type key = bytes

val get : bytes -> Rval.t
val put : bytes -> Rval.t -> unit
val run : Rval.t T.t -> (unit -> 'a) -> 'a
