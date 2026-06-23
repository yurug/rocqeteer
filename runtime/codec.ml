(** Runtime Codec realizer: a typed binary encoder/decoder over real [bytes], using a GADT
    witness so encode/decode are type-indexed with no unsafe casts (kb/architecture/decisions/
    adr-0004-trust-model.md, report §9/§18). The round-trip is PROVEN for the reference token
    format in theories/Codec.v; this bytes realizer is property-tested (tests/codec_test.ml).

    Format: an [EInt] is a 1-byte decimal length followed by that many ASCII digit bytes; a
    pair is the concatenation of its components. *)

type _ enc =
  | EInt : Z.t enc
  | EPair : 'a enc * 'b enc -> ('a * 'b) enc

exception Malformed of string

(* [type a.] gives polymorphic recursion so the GADT refines per constructor — no cast. *)
let rec encode_into : type a. a enc -> a -> Buffer.t -> unit =
 fun e v buf ->
  match (e, v) with
  | EInt, z ->
      let s = Z.to_string z in
      if String.length s > 255 then raise (Malformed "EInt: too wide for a 1-byte length");
      Buffer.add_uint8 buf (String.length s);
      Buffer.add_string buf s
  | EPair (e1, e2), (a, b) ->
      encode_into e1 a buf;
      encode_into e2 b buf

let to_bytes (e : 'a enc) (v : 'a) : bytes =
  let buf = Buffer.create 16 in
  encode_into e v buf;
  Buffer.to_bytes buf

let rec decode_at : type a. a enc -> bytes -> int -> a * int =
 fun e bs pos ->
  match e with
  | EInt ->
      if pos >= Bytes.length bs then raise (Malformed "EInt: missing length byte");
      let len = Bytes.get_uint8 bs pos in
      if pos + 1 + len > Bytes.length bs then raise (Malformed "EInt: truncated payload");
      (Z.of_string (Bytes.sub_string bs (pos + 1) len), pos + 1 + len)
  | EPair (e1, e2) ->
      let a, p1 = decode_at e1 bs pos in
      let b, p2 = decode_at e2 bs p1 in
      ((a, b), p2)

(** Total at the boundary: malformed input becomes [Error], never a crash (edge case T9). *)
let of_bytes (e : 'a enc) (bs : bytes) : ('a, string) result =
  try Ok (fst (decode_at e bs 0)) with
  | Malformed m -> Error m
  | _ -> Error "decode failed"
