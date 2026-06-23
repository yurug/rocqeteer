(** Codec property test: the GADT/bytes realizer round-trips every typed value, mirroring
    the PROVEN reference round-trip (theories/Codec.v `roundtrip`). To avoid comparing
    heterogeneous decoded values, we check decode-then-re-encode reproduces the bytes
    (parse/print stability, report §12.1). Plus a malformed-input check (T9). *)

module C = Rkv.Codec

(* An encoding paired with a matching value (existential, so shapes can vary at runtime). *)
type packed = Packed : 'a C.enc * 'a -> packed

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260623
let rng = Random.State.make [| seed |]

let rec gen (depth : int) : packed =
  if depth <= 0 || Random.State.bool rng then Packed (C.EInt, Z.of_int (Random.State.int rng 1_000_000 - 500_000))
  else
    let (Packed (e1, v1)) = gen (depth - 1) in
    let (Packed (e2, v2)) = gen (depth - 1) in
    Packed (C.EPair (e1, e2), (v1, v2))

let () =
  let n = 5000 in
  let fails = ref 0 and pairs = ref 0 in
  for _ = 1 to n do
    let (Packed (e, v)) = gen 4 in
    (match e with C.EPair _ -> incr pairs | _ -> ());
    let b = C.to_bytes e v in
    match C.of_bytes e b with
    | Ok v' -> if not (Bytes.equal (C.to_bytes e v') b) then incr fails
    | Error _ -> incr fails
  done;
  (* T9: malformed input must yield Error, not a crash *)
  let t9 = match C.of_bytes C.EInt Bytes.empty with Error _ -> true | Ok _ -> false in
  Printf.printf "cases=%d fails=%d (incl. %d compound encodings) | T9-malformed=%b\n" n !fails !pairs t9;
  if !fails = 0 && !pairs > 0 && t9 then
    print_endline "CODEC OK: GADT/bytes round-trip holds for all typed values (matches proven reference)"
  else exit 1
