(** OCaml realizers for the v1 primitive set (adr-0009-vprim-registry §Decision 4+5).

    Each function is written FROM the corresponding Rocq reference definition in
    theories/EffIR.v — the decision points are in the same order, with matching names.
    No exceptions escape; all functions are total, returning [Rval.t] where [Rval.None]
    corresponds to [DNone] and [Rval.Some v] corresponds to [DSome v], matching the
    [opt_to_rval] convention used in [kv.ml].

    Realizer naming convention: [prim_<name>] (one exported symbol per prim, as per
    ADR §5); codegen emits [Prims.prim_<name>].

    The [in_range] check mirrors [EffIR.in_range]: [-2^63, 2^63-1]. *)

let int64_min : Z.t = Z.of_string "-9223372036854775808"
let int64_max : Z.t = Z.of_string "9223372036854775807"

(** [in_range z]: true iff z is in [int64_min, int64_max].
    Mirrors [EffIR.in_range]. *)
let in_range (z : Z.t) : bool =
  Z.leq int64_min z && Z.leq z int64_max

(** [prim_add_checked a b]: Z addition, [Rval.None] if result leaves int64 range.
    Mirrors [EffIR.apply_add_checked]. *)
let prim_add_checked (a : Rval.t) (b : Rval.t) : Rval.t =
  match a, b with
  | Rval.Int za, Rval.Int zb ->
      let r = Z.add za zb in
      if in_range r then Rval.Some (Rval.Int r)
      else Rval.None
  | _ -> Rval.None  (* shape mismatch *)

(** [prim_sub_checked a b]: Z subtraction, [Rval.None] if result leaves int64 range.
    Mirrors [EffIR.apply_sub_checked]. *)
let prim_sub_checked (a : Rval.t) (b : Rval.t) : Rval.t =
  match a, b with
  | Rval.Int za, Rval.Int zb ->
      let r = Z.sub za zb in
      if in_range r then Rval.Some (Rval.Int r)
      else Rval.None
  | _ -> Rval.None

(** [prim_cmp_int a b]: total three-way comparison; result is [Rval.Int (-1|0|1)].
    Mirrors [EffIR.apply_cmp_int]. *)
let prim_cmp_int (a : Rval.t) (b : Rval.t) : Rval.t =
  match a, b with
  | Rval.Int za, Rval.Int zb ->
      let c = Z.compare za zb in
      Rval.Int (if c < 0 then Z.of_int (-1) else if c > 0 then Z.one else Z.zero)
  | _ -> Rval.None

(** [prim_eq_bytes a b]: byte equality; result is [Rval.Bool].
    Mirrors [EffIR.ascii_list_eqb]. *)
let prim_eq_bytes (a : Rval.t) (b : Rval.t) : Rval.t =
  match a, b with
  | Rval.Bytes ba, Rval.Bytes bb -> Rval.Bool (Bytes.equal ba bb)
  | _ -> Rval.None

(** [prim_bytes_len bs]: length of byte string; result is [Rval.Int].
    Mirrors [EffIR.apply_prim PBytesLen]. *)
let prim_bytes_len (bs : Rval.t) : Rval.t =
  match bs with
  | Rval.Bytes b -> Rval.Int (Z.of_int (Bytes.length b))
  | _ -> Rval.None

(** [prim_bytes_concat a b]: concatenate two byte strings; result is [Rval.Bytes].
    Mirrors [EffIR.apply_prim PBytesConcat]. *)
let prim_bytes_concat (a : Rval.t) (b : Rval.t) : Rval.t =
  match a, b with
  | Rval.Bytes ba, Rval.Bytes bb ->
      let la = Bytes.length ba and lb = Bytes.length bb in
      let r = Bytes.create (la + lb) in
      Bytes.blit ba 0 r 0 la;
      Bytes.blit bb 0 r la lb;
      Rval.Bytes r
  | _ -> Rval.None

(** [prim_bytes_sub bs offset len]: slice; [Rval.None] if out of range.
    Mirrors [EffIR.apply_bytes_sub].
    Decision points:
      DS1: offset < 0 → None
      DS2: len < 0 → None
      DS3: offset + len > |bs| → None
      DS4: otherwise → Some (Rval.Bytes slice) *)
let prim_bytes_sub (bs : Rval.t) (offset : Rval.t) (len : Rval.t) : Rval.t =
  match bs, offset, len with
  | Rval.Bytes b, Rval.Int zoff, Rval.Int zlen ->
      let n = Bytes.length b in
      (* DS1: offset < 0 *)
      if Z.sign zoff < 0 then Rval.None
      (* DS2: len < 0 *)
      else if Z.sign zlen < 0 then Rval.None
      (* DS3: offset + len > n — checked in Z, like the Rocq reference, BEFORE any int
         conversion: an offset/len beyond native-int range must be rejected here, not
         raise Z.Overflow (and off + l on native int could wrap). *)
      else if Z.gt (Z.add zoff zlen) (Z.of_int n) then Rval.None
      (* DS4: valid slice — offset and len now provably fit in int (both <= n) *)
      else Rval.Some (Rval.Bytes (Bytes.sub b (Z.to_int zoff) (Z.to_int zlen)))
  | _ -> Rval.None

(** [is_digit c]: ASCII '0'–'9' (mirrors [EffIR.is_digit]).
    DP component shared by parse. *)
let is_digit (c : char) : bool =
  let n = Char.code c in n >= 48 && n <= 57

(** [digit_val c]: numeric value of ASCII digit (mirrors [EffIR.digit_val]). *)
let digit_val (c : char) : int = Char.code c - 48

(** [parse_digits s start]: fold digit characters of [s] from position [start] onward
    into a Z, checking all chars are digits (mirrors [EffIR.parse_digits]).
    Returns [None] if any non-digit found. *)
let parse_digits (s : bytes) (start : int) (len : int) : Z.t option =
  let ok = ref true in
  let acc = ref Z.zero in
  for i = start to start + len - 1 do
    let c = Bytes.get s i in
    if not (is_digit c) then ok := false
    else acc := Z.add (Z.mul !acc (Z.of_int 10)) (Z.of_int (digit_val c))
  done;
  if !ok then Some !acc else None

(** [prim_parse_int64 bs]: STRICT decimal parse (mirrors [EffIR.apply_parse_int64]).
    Decision points in the SAME ORDER as the Rocq definition:
      DP1: empty input → None
      DP2: leading '-' → set negative flag, advance past it
      DP3: digits empty after sign → None  (bare '-')
      DP4: leading '0' → must be exactly "0"; if more chars → None (leading-zero violation)
            "-0" → None (not canonical)
      DP5: leading non-digit ('+', space, other) → None
      DP6: parse all remaining digits; non-digit in body → None
      DP7: apply sign
      DP8: range check → None if outside int64 *)
let prim_parse_int64 (bs : Rval.t) : Rval.t =
  match bs with
  | Rval.Bytes b ->
      let n = Bytes.length b in
      (* DP1: empty *)
      if n = 0 then Rval.None
      else begin
        let c0 = Bytes.get b 0 in
        (* DP2: sign detection *)
        let negative = c0 = '-' in
        let dstart = if negative then 1 else 0 in
        let dlen = n - dstart in
        (* DP3: digits empty after sign *)
        if dlen = 0 then Rval.None
        else begin
          let d0 = Bytes.get b dstart in
          (* DP5: leading non-digit (incl. '+', space, etc.) *)
          if not (is_digit d0) then Rval.None
          (* DP4: leading zero rule *)
          else if d0 = '0' then begin
            if dlen = 1 then begin
              (* exactly "0" or "-0" *)
              if negative then Rval.None  (* "-0" not canonical *)
              else Rval.Some (Rval.Int Z.zero)
            end else
              Rval.None  (* "0..." with trailing chars → leading-zero violation *)
          end else begin
            (* DP6: non-zero leading digit — parse all digits *)
            match parse_digits b dstart dlen with
            | None -> Rval.None  (* non-digit in body *)
            | Some magnitude ->
                (* DP7: apply sign *)
                let z = if negative then Z.neg magnitude else magnitude in
                (* DP8: range check *)
                if in_range z then Rval.Some (Rval.Int z)
                else Rval.None
          end
        end
      end
  | _ -> Rval.None

(** [prim_print_int z]: canonical decimal of an in-range DInt; [Rval.None] if out of range.
    Mirrors [EffIR.apply_print_int].
    Grammar: optional '-', digits with no leading zeros, "0" for zero. *)
let prim_print_int (v : Rval.t) : Rval.t =
  match v with
  | Rval.Int z ->
      if not (in_range z) then Rval.None
      else
        let s = Z.to_string z in  (* zarith produces the canonical decimal string *)
        Rval.Some (Rval.Bytes (Bytes.of_string s))
  | _ -> Rval.None

(** [prim_mul_checked a b]: Z multiplication, [Rval.None] if result leaves int64 range.
    Mirrors [EffIR.apply_mul_checked] (R6, adr-0012). NB the asymmetric boundary:
    -1 * int64_min = 2^63 > int64_max -> None. *)
let prim_mul_checked (a : Rval.t) (b : Rval.t) : Rval.t =
  match a, b with
  | Rval.Int za, Rval.Int zb ->
      let r = Z.mul za zb in
      if in_range r then Rval.Some (Rval.Int r)
      else Rval.None
  | _ -> Rval.None  (* shape mismatch *)

(** [prim_list_len l]: length of a list value; result is [Rval.Int].
    Mirrors [EffIR.apply_prim PListLen] (R6, adr-0012). *)
let prim_list_len (l : Rval.t) : Rval.t =
  match l with
  | Rval.List vs -> Rval.Int (Z.of_int (List.length vs))
  | _ -> Rval.None

(** [prim_list_nth l i]: the i-th element (0-based), option-encoded.
    Mirrors [EffIR.apply_list_nth] (R6, adr-0012).
    Decision points:
      DN1: i < 0            -> None
      DN2: length <= i      -> None  (checked in Z, like the Rocq reference, BEFORE any
                                      int conversion — an index beyond native-int range
                                      must be rejected here, not raise Z.Overflow; the
                                      prim_bytes_sub DS3 lesson above)
      DN3: otherwise        -> Some v_i (i now provably fits in int: i < length) *)
(** [prim_div_floor a b]: FLOOR division, option-encoded (R9 companion prim,
    adr-0009 discipline). Mirrors [EffIR.apply_div_floor]: Rocq's [Z.div] IS floor
    division (rounds toward -infinity: (-7)/2 = -4), so this realizer uses zarith's
    [Z.fdiv] — zarith's [Z.div] TRUNCATES toward zero and differs on negative
    dividends ((-7)/2 would be -3). Division by zero returns [Rval.None] — total, no
    exception (the b = 0 guard runs before any division). Consumer driver: TTL-style
    rounding, e.g. (pttl + 500) / 1000. Range-checked like the Checked family: the one
    int64-range escape, int64_min / -1 = 2^63, returns [Rval.None]. *)
let prim_div_floor (a : Rval.t) (b : Rval.t) : Rval.t =
  match a, b with
  | Rval.Int za, Rval.Int zb ->
      if Z.equal zb Z.zero then Rval.None
      else
        let r = Z.fdiv za zb in
        if in_range r then Rval.Some (Rval.Int r) else Rval.None
  | _ -> Rval.None  (* shape mismatch *)

let prim_list_nth (l : Rval.t) (i : Rval.t) : Rval.t =
  match l, i with
  | Rval.List vs, Rval.Int zi ->
      (* DN1: i < 0 *)
      if Z.sign zi < 0 then Rval.None
      (* DN2: length <= i — in Z, before Z.to_int *)
      else if Z.leq (Z.of_int (List.length vs)) zi then Rval.None
      (* DN3: in bounds *)
      else Rval.Some (List.nth vs (Z.to_int zi))
  | _ -> Rval.None
