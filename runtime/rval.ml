(** Runtime value universe mirroring theories/EffIR.v [dval].

    Constructor correspondence (dval → Rval.t):
      DUnit          → Unit
      DBool b        → Bool b
      DInt z         → Int z
      DNone          → None
      DSome v        → Some v
      DPair (a, b)   → Pair (a, b)
      DBytes bs      → Bytes bs
      DTag (z, v)    → Tag (z, v)     (R7, adr-0010-structured-values)
      DList vs       → List vs        (R7, adr-0010-structured-values; no elimination until R6)
      Dstuck         → Stuck exception

    A new dval constructor MUST be added here in the same commit. *)

type t =
  | Unit
  | Bool  of bool
  | Int   of Z.t
  | None
  | Some  of t
  | Pair  of t * t
  | Bytes of bytes
  | Tag   of Z.t * t
  | List  of t list

exception Stuck

let rec equal a b =
  match a, b with
  | Unit,      Unit      -> true
  | Bool x,    Bool y    -> x = y
  | Int  x,    Int  y    -> Z.equal x y
  | None,      None      -> true
  | Some x,    Some y    -> equal x y
  | Pair(a1,b1), Pair(a2,b2) -> equal a1 a2 && equal b1 b2
  | Bytes x,   Bytes y   -> Bytes.equal x y
  | Tag(t1,v1), Tag(t2,v2) -> Z.equal t1 t2 && equal v1 v2
  | List xs,   List ys   ->
      (* Length mismatch = false (adr-0010 §Decision 4); otherwise pointwise [equal]. *)
      (try List.for_all2 equal xs ys with Invalid_argument _ -> false)
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
  | Pair _,  _       -> -1
  | _,       Pair _  -> 1
  | Bytes x, Bytes y -> Bytes.compare x y
  | Bytes _, _       -> -1
  | _,       Bytes _ -> 1
  | Tag(t1,v1), Tag(t2,v2) ->
      let c = Z.compare t1 t2 in if c <> 0 then c else compare v1 v2
  | Tag _,   _       -> -1
  | _,       Tag _   -> 1
  | List xs, List ys -> compare_list xs ys

and compare_list xs ys =
  match xs, ys with
  | [],       []       -> 0
  | [],       _        -> -1
  | _,        []       -> 1
  | x :: xs', y :: ys' ->
      let c = compare x y in if c <> 0 then c else compare_list xs' ys'

(** Hex-escaped rendering for binary-hostile content: each byte as \xNN. *)
let bytes_to_escaped (b : bytes) : string =
  let buf = Buffer.create (Bytes.length b * 4) in
  Bytes.iter (fun c ->
    let n = Char.code c in
    if n >= 0x20 && n <= 0x7E && c <> '"' && c <> '\\' then
      Buffer.add_char buf c
    else (
      Buffer.add_string buf "\\x";
      Buffer.add_string buf (Printf.sprintf "%02x" n))
  ) b;
  Buffer.contents buf

let rec to_string = function
  | Unit       -> "()"
  | Bool true  -> "true"
  | Bool false -> "false"
  | Int  z     -> Z.to_string z
  | None       -> "None"
  | Some v     -> "Some(" ^ to_string v ^ ")"
  | Pair(a, b) -> "(" ^ to_string a ^ ", " ^ to_string b ^ ")"
  | Bytes b    -> "Bytes(\"" ^ bytes_to_escaped b ^ "\")"
  | Tag(z, v)  -> "Tag(" ^ Z.to_string z ^ ", " ^ to_string v ^ ")"
  | List vs    -> "[" ^ String.concat "; " (List.map to_string vs) ^ "]"
