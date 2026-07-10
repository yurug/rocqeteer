(** Runtime value universe mirroring theories/EffIR.v [dval].

    Constructor correspondence (dval → Rval.t):
      DUnit          → Unit
      DBool b        → Bool b
      DInt z         → Int z
      DNone          → None
      DSome v        → Some v
      DPair (a, b)   → Pair (a, b)
      Dstuck         → Stuck exception

    A new dval constructor MUST be added here in the same commit. *)

type t =
  | Unit
  | Bool of bool
  | Int  of Z.t
  | None
  | Some of t
  | Pair of t * t

exception Stuck

let rec equal a b =
  match a, b with
  | Unit,      Unit      -> true
  | Bool x,    Bool y    -> x = y
  | Int  x,    Int  y    -> Z.equal x y
  | None,      None      -> true
  | Some x,    Some y    -> equal x y
  | Pair(a1,b1), Pair(a2,b2) -> equal a1 a2 && equal b1 b2
  | _ -> false

let rec compare a b =
  match a, b with
  | Unit,    Unit    -> 0
  | Unit,    _       -> -1
  | _,       Unit    -> 1
  | Bool x,  Bool y  -> Bool.compare x y
  | Bool _,  _       -> -1
  | _,       Bool _  -> 1
  | Int  x,  Int  y  -> Z.compare x y
  | Int  _,  _       -> -1
  | _,       Int  _  -> 1
  | None,    None    -> 0
  | None,    _       -> -1
  | _,       None    -> 1
  | Some x,  Some y  -> compare x y
  | Some _,  _       -> -1
  | _,       Some _  -> 1
  | Pair(a1,b1), Pair(a2,b2) ->
      let c = compare a1 a2 in if c <> 0 then c else compare b1 b2

let rec to_string = function
  | Unit       -> "()"
  | Bool true  -> "true"
  | Bool false -> "false"
  | Int  z     -> Z.to_string z
  | None       -> "None"
  | Some v     -> "Some(" ^ to_string v ^ ")"
  | Pair(a, b) -> "(" ^ to_string a ^ ", " ^ to_string b ^ ")"
