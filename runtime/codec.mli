(** Typed binary codec realizer (GADT witness, no unsafe casts). The round-trip is proven for
    the reference format in theories/Codec.v; this bytes realizer is property-tested. *)

type _ enc =
  | EInt : Z.t enc
  | EPair : 'a enc * 'b enc -> ('a * 'b) enc

val to_bytes : 'a enc -> 'a -> bytes
val of_bytes : 'a enc -> bytes -> ('a, string) result
