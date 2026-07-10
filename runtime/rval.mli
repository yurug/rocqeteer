(** Runtime value universe mirroring theories/EffIR.v [dval].

    This type has a ONE-FOR-ONE correspondence with every [dval] constructor.
    A new [dval] constructor MUST be added here in the same commit.

    Constructor correspondence (dval → Rval.t):
      DUnit          → Unit
      DBool b        → Bool b
      DInt z         → Int z          (zarith Z.t, not Coq coq_Z)
      DNone          → None
      DSome v        → Some v
      DPair (a, b)   → Pair (a, b)
      Dstuck         → (see Stuck exception below)

    [Dstuck] is represented as an exception rather than a constructor so that
    the type [Rval.t] carries only well-formed values and stuck computations
    are surfaced at the effect boundary (mirrors the reference interpreter:
    Dstuck is never produced for well-typed closed terms, but we expose the
    failure for ill-typed generated code rather than silently coercing). *)

type t =
  | Unit
  | Bool of bool
  | Int  of Z.t
  | None
  | Some of t
  | Pair of t * t

(** Raised by generated code when a value of an unexpected shape is
    encountered (e.g. [Z.succ] applied to a non-[Int] value).  Mirrors
    the reference interpreter's [Dstuck] sentinel on ill-typed cases. *)
exception Stuck

val equal     : t -> t -> bool
val compare   : t -> t -> int
val to_string : t -> string
