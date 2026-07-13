(** * EffIR — first-order effect IR (v2, R9: Journal effect — append-only (now_ms, dval)
    log) and its reference semantics.

    This is the SINGLE representation that the reference interpreter (here) evaluates
    and that the codegen lowers (after extraction to an OCaml ADT). Keeping one
    extrinsically-typed, first-order datatype is what guarantees "the program proved =
    the program run" — see kb/architecture/decisions/adr-0001-first-order-ast.md and
    kb/spec/effir.md.

    IR v2 R2 (2026-07-10, adr-0008-general-match): [MatchOpt] is replaced by the
    general [Match] form with depth-1 patterns, mandatory default arm, first-match-wins
    semantics, and no typechecker assumption for totality.

    IR v2 R3 (2026-07-10, adr-0009-vprim-registry): [Prim] term added — a closed first-order
    set of total primitives. Fallible operations return option-encoded dvals (DNone / DSome).
    The [prim] inductive enumerates the v1 set; [apply_prim] is the TOTAL reference
    definition; [run] handles the [Prim] case by evaluating args then applying [apply_prim].

    IR v2 R7 (2026-07-11, adr-0010-structured-values): [dval]/[val] gain [DTag]/[VTag]
    (a Z-tagged sum injection) and [DList]/[VList] (a finite sequence of values); [pat]
    gains [PTag] (depth-1, literal tag, binds the single payload). [DList] is
    constructible and observable but has NO IR-level elimination until R6 — consumers
    traverse it in their own pure Gallina after the boundary.

    IR v2 R4+R5 (2026-07-11, adr-0011-time-and-expiring-store): the Z-keyed KV is
    REPLACED by an expiring, byte-string-keyed store — [world.kv] maps string keys
    (converted from [list ascii] at the op boundary) to [(dval * option Z)] (value +
    optional absolute deadline in ms). Liveness is the ONE rule: a binding [(v, Some d)]
    is live iff [now_ms <= d] (alive AT the deadline, dead strictly after); [(v, None)]
    is always live; expired bindings are semantically ABSENT for every op and for
    [observe]. [world] gains [now_ms : Z], immutable within a run ([run_top] takes it);
    the new [Time] effect exposes it via [ONow]. Ops: [OGet]/[OPut]/[ODelete] re-shaped
    to bytes keys ([OPut] CLEARS any deadline; [ODelete] returns whether a LIVE binding
    was removed), plus [OGetDeadline]/[OSetDeadline]. Cache keys migrate to bytes too
    (one key discipline across the value-keyed effects).

    IR v2 R6 (2026-07-12, adr-0012-list-elimination): [Fold] term added — the ONE list
    elimination form, an accumulator fold BOUNDED BY THE LIST (totality is structural on
    the finite [DList]; no fuel, no static bound). [Fold lst init body]: evaluate [lst];
    run [init] for the starting accumulator; for each element LEFT TO RIGHT run [body] in
    the environment extended via [push_env [elem; acc]] (acc at de Bruijn 0, element at
    de Bruijn 1); [body]'s result is the next accumulator. [OErr] from [init] or any
    iteration short-circuits (Bind discipline); the world threads through iterations. A
    non-[DList] scrutinee makes the fold EMPTY (result = [init]'s result) — total without
    a typechecker, same posture as prim shape mismatch; R10 rejects it statically. Prims
    gain [PListLen]/[PListNth] (arity checks + indexed access) and [PMulChecked] (checked
    multiplication, e.g. seconds->ms scaling — same total/option-encoded style as
    [PAddChecked]). No PNil/PCons patterns in v1 (adr-0012 §Decision 4).

    IR v2 R9 (2026-07-12, adr-0013-journal-effect): the Journal effect — [world] gains
    [journal : list (Z * dval)] (newest-first, the Trace convention) and the one op
    [OJournal [v] -> DUnit] appends [(now_ms, eval v)]. The timestamp is the run's single
    instant (adr-0011: no in-IR clock advancement), so entries within one run share it by
    design. NO op reads the journal — it is write-only by construction; the frame law
    (a run's outcome and non-journal observables are independent of the initial journal,
    and the final journal is new-entries ++ initial) is proven GENERALLY in
    theories/Journal.v ([run_journal_frame]), alongside the run-sequence-is-a-fold
    composition lemma. [observe_full] exposes the journal reversed (chronological),
    alongside the trace. Also adds the prim [PDivFloor] (adr-0009 discipline: ADR-free,
    manifest + diff-test mandatory) — FLOOR division, option-encoded division by zero.

    IR v2 R12 (2026-07-13, adr-0009 discipline — ADR-free prim addition, manifest +
    diff-test mandatory): [PLowerBytes]/[PUpperBytes] — ASCII case folding, arity 1,
    [DBytes bs] -> [DBytes] with bytes 65-90 ('A'-'Z') shifted +32 (lower) resp. bytes
    97-122 ('a'-'z') shifted -32 (upper); EVERY other byte unchanged, including bytes
    > 127 (a pure ASCII fold: no locale, no UTF-8). Total; shape mismatch -> DNone.
    Consumer driver: case-insensitive command option tokens (inexpressible with the
    exact [PEqBytes]).

    IR v2 R13 (2026-07-13, adr-0009 discipline — ADR-free prim addition, manifest +
    diff-test mandatory): [PListSnoc] — the minimal list-CONSTRUCTION capability,
    arity 2, [DList vs; v] -> [DList (vs ++ [v])]: append [v] at the END. The appended
    element is ANY dval (incl. another [DList]/[DTag] — replies nest); a first argument
    that is not a [DList] -> DNone (the adr-0009 shape posture). Total, order-preserving.
    Consumer driver: building replies of DATA-DEPENDENT length — [Fold] (R6) can
    eliminate lists but nothing constructs one whose length is runtime-determined; a
    collecting fold (acc = the DList under construction, body snocs) closes the gap with
    ZERO new term forms ([sample_fold_collect], proven in theories/Fold.v §9). *)

From Stdlib Require Import ZArith List FMapAVL OrderedTypeEx Ascii String Bool.
Import ListNotations.
Local Open Scope Z_scope.

(** Boolean equality on [ascii], avoiding the Stdlib [Ascii.eqb] which can create
    extraction issues when [Bool] is opened in the generated code. We compare the eight
    bits directly via [Bool.eqb]. *)
Definition ascii_eqb (a b : ascii) : bool :=
  match a, b with
  | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
    Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      Bool.eqb a0 b0 && Bool.eqb a1 b1 && Bool.eqb a2 b2 && Bool.eqb a3 b3
   && Bool.eqb a4 b4 && Bool.eqb a5 b5 && Bool.eqb a6 b6 && Bool.eqb a7 b7
  end.

(** Boolean equality on [list ascii], used by [match_pat] for [PBytes] matching. *)
Fixpoint ascii_list_eqb (xs ys : list ascii) : bool :=
  match xs, ys with
  | [], []             => true
  | x :: xs', y :: ys' => ascii_eqb x y && ascii_list_eqb xs' ys'
  | _, _               => false
  end.

(** A STRING-keyed finite map is the reference store state (R4, adr-0011): keys are byte
    strings, ordered by the stdlib [String_as_OT] (lexicographic on character codes — the
    same order as OCaml's [Bytes.compare], so sorted [elements] is exactly the
    order-independent observable the differential test compares against the OCaml Hashtbl;
    kb/spec/reference-semantics.md). The [list ascii] byte payloads of [VBytes]/[DBytes]
    convert to [string] keys at the op boundary via [string_of_list_ascii]. *)
Module M := FMapAVL.Make(String_as_OT).

(** ** Runtime values (dynamically typed).
    The interpreter is total; [Dstuck] marks an impossible/ill-typed case that proofs
    discharge as unreachable for well-typed closed terms (kb/plan.md Resolution 2). *)
Inductive dval : Type :=
| DUnit  : dval
| DBool  : bool -> dval
| DInt   : Z -> dval
| DNone  : dval
| DSome  : dval -> dval
| DPair  : dval -> dval -> dval
| DBytes : list ascii -> dval
| DTag   : Z -> dval -> dval      (** constructor-tagged value: sum injection (R7) *)
| DList  : list dval -> dval      (** finite sequence of values (R7, no elimination until R6) *)
| Dstuck : dval.

(** ** Pure first-order expressions. [VVar] is a de Bruijn index.
    [VZero]/[VSucc] are the slice-1 pure prims (realized to Z.zero / Z.succ). *)
Inductive val : Type :=
| VVar  : nat -> val
| VUnit : val
| VBool : bool -> val
| VInt  : Z -> val
| VNone : val
| VSome : val -> val
| VPair : val -> val -> val
| VZero   : val
| VSucc   : val -> val
| VBytes  : list ascii -> val
| VTag    : Z -> val -> val        (** builds a DTag (R7, adr-0010-structured-values) *)
| VList   : list val -> val.       (** builds a DList (R7, adr-0010-structured-values) *)

(** ** Effect operations: Store (Get/Put/Delete/GetDeadline/SetDeadline — the expiring
    bytes-keyed store, R4), [ONow] (Time, R5), [OThrow] (Error), [OAsk] (Env), [OTrace]
    (Trace), [OCacheGet]/[OCachePut] (Cache — a memo store kept OUT of [observe], so it
    is observationally invisible), and [OJournal] (Journal, R9 — append-only, write-only:
    no op reads it back) — kb/spec/effect-signatures.md, adr-0011, adr-0013. *)
Inductive op : Type :=
  | OGet | OPut | ODelete | OGetDeadline | OSetDeadline | ONow
  | OThrow | OAsk | OTrace | OCacheGet | OCachePut | OJournal.

(** ** Closed v1 primitive set (adr-0009-vprim-registry §Decision 3).
    All prims are TOTAL: fallible ones return option-encoded dvals (DNone/DSome) so that
    the [Match] form handles failure — no new error machinery needed.
    Arity or shape mismatch yields [DNone] (the R10 typechecker will reject such programs
    statically; semantics stays total meanwhile). *)
Inductive prim : Type :=
| PAddChecked   (** DInt a, DInt b -> DSome (DInt (a+b)) if in-range, DNone otherwise *)
| PSubChecked   (** DInt a, DInt b -> DSome (DInt (a-b)) if in-range, DNone otherwise *)
| PCmpInt       (** DInt a, DInt b -> DInt (-1 | 0 | 1) *)
| PEqBytes      (** DBytes a, DBytes b -> DBool (equality) *)
| PBytesLen     (** DBytes bs -> DInt (length) *)
| PBytesConcat  (** DBytes a, DBytes b -> DBytes (a ++ b) *)
| PBytesSub     (** DBytes bs, DInt offset, DInt len -> DSome (DBytes slice) or DNone if OOB *)
| PParseInt64   (** DBytes bs -> DSome (DInt z) under strict grammar, else DNone *)
| PPrintInt     (** DInt z -> DSome (DBytes decimal) if in-range, DNone if not *)
| PMulChecked   (** DInt a, DInt b -> DSome (DInt (a*b)) if in-range, DNone otherwise (R6) *)
| PListLen      (** DList vs -> DInt (length vs); shape mismatch -> DNone (R6) *)
| PListNth      (** DList vs, DInt i -> DSome v_i if 0 <= i < len; DNone otherwise (R6) *)
| PDivFloor     (** DInt a, DInt b -> DNone if b = 0, else DSome (DInt (a / b)) — FLOOR (R9) *)
| PLowerBytes   (** DBytes bs -> DBytes (ASCII fold: 65-90 shifted +32; every other byte unchanged) (R12) *)
| PUpperBytes   (** DBytes bs -> DBytes (ASCII fold: 97-122 shifted -32; every other byte unchanged) (R12) *)
| PListSnoc.    (** DList vs, v -> DList (vs ++ [v]) — v is ANY dval; non-DList first arg -> DNone (R13) *)

(** Int64 bounds: [−2⁶³, 2⁶³−1] as explicit Z constants. *)
Definition int64_min : Z := -9223372036854775808.
Definition int64_max : Z :=  9223372036854775807.

Definition in_range (z : Z) : bool :=
  Z.leb int64_min z && Z.leb z int64_max.

(** [apply_add_checked a b]: Z addition, DNone if result leaves int64 range. *)
Definition apply_add_checked (a b : Z) : dval :=
  let r := a + b in
  if in_range r then DSome (DInt r) else DNone.

(** [apply_sub_checked a b]: Z subtraction, DNone if result leaves int64 range. *)
Definition apply_sub_checked (a b : Z) : dval :=
  let r := a - b in
  if in_range r then DSome (DInt r) else DNone.

(** [apply_mul_checked a b]: Z multiplication, DNone if result leaves int64 range (R6,
    adr-0012). NB the asymmetric boundary: [int64_min * -1 = 2^63 > int64_max] -> DNone. *)
Definition apply_mul_checked (a b : Z) : dval :=
  let r := a * b in
  if in_range r then DSome (DInt r) else DNone.

(** [apply_list_nth vs i]: the i-th element of [vs] (0-based), option-encoded (R6,
    adr-0012 §Decision 3): DSome v_i if 0 <= i < length vs, DNone otherwise. The bounds
    check is in Z; only an in-bounds index is converted to nat. *)
Definition apply_list_nth (vs : list dval) (i : Z) : dval :=
  if (i <? 0) || (Z.of_nat (List.length vs) <=? i)
  then DNone
  else match List.nth_error vs (Z.to_nat i) with
       | Some v => DSome v
       | None   => DNone   (* unreachable: the bound check guarantees in-range *)
       end.

(** [apply_div_floor a b]: FLOOR division, option-encoded (R9 companion prim; adr-0009
    discipline — ADR-free addition, manifest + diff-test mandatory). CONFIRMED: Rocq's
    [Z.div] IS floor division (rounds toward -infinity: (-7)/2 = -4, 7/(-2) = -4; the
    truncating variant is [Z.quot]) — the OCaml realizer must therefore use zarith's
    [Z.fdiv], because zarith's [Z.div] truncates toward zero and DIFFERS on negative
    dividends. Division by zero is total here: [DNone] (option-encoded failure, no
    exception — the [Match] form handles it). Consumer driver: TTL-style rounding,
    e.g. (pttl + 500) / 1000. Range-checked like the rest of the Checked family: with
    int64-range inputs the only escaping result is int64_min / -1 = 2^63 -> DNone
    (convention consistency over cleverness; R10 may bound it statically). *)
Definition apply_div_floor (a b : Z) : dval :=
  if b =? 0 then DNone
  else let r := a / b in
       if in_range r then DSome (DInt r) else DNone.

(** [apply_cmp_int a b]: total three-way comparison; result is DInt −1, 0, or 1. *)
Definition apply_cmp_int (a b : Z) : dval :=
  match Z.compare a b with
  | Lt => DInt (-1)
  | Eq => DInt 0
  | Gt => DInt 1
  end.

(** [is_digit c]: c is ASCII '0'–'9'. *)
Definition is_digit (c : ascii) : bool :=
  let n := N_of_ascii c in
  (48 <=? n)%N && (n <=? 57)%N.

(** [digit_val c]: the numeric value of ASCII digit c (0–9). *)
Definition digit_val (c : ascii) : Z :=
  Z.of_N (N_of_ascii c) - Z.of_N 48.

(** [parse_digits cs acc]: fold a non-empty list of digit ascii chars into a Z value.
    Accumulates left-to-right (most significant first). *)
Fixpoint parse_digits (cs : list ascii) (acc : Z) : Z :=
  match cs with
  | []      => acc
  | c :: rest => parse_digits rest (acc * 10 + digit_val c)
  end.

(** [apply_parse_int64 bs]: STRICT decimal parse (adr-0009 §Context + §Decision 3):
    Grammar:
      1. Optional leading '-'
      2. "0" (exact) OR a nonzero digit followed by zero or more digits
      3. ENTIRE input consumed (no trailing characters)
      4. Result in [int64_min, int64_max]
    Any violation → DNone. No '+', no whitespace, no leading zeros (except "0" itself),
    no empty input, no non-digit characters.

    Decision points implemented in order:
      DP1: empty input  → DNone
      DP2: leading '-'  → negate; advance; must have at least one digit after
      DP3: digits empty → DNone (handles "-" with nothing after)
      DP4: leading '0'  → must be exactly "0" (no "0123"); if more chars after → DNone
      DP5: leading '+', space, or any non-digit → DNone
      DP6: parse the digit sequence
      DP7: sign applied
      DP8: range check → DNone if outside int64 *)
Definition apply_parse_int64 (bs : list ascii) : dval :=
  match bs with
  | [] => DNone  (* DP1: empty *)
  | c0 :: rest =>
      (* DP2: detect sign *)
      let '(negative, digits) :=
        if ascii_eqb c0 (ascii_of_N 45)  (* '-' *)
        then (true, rest)
        else (false, bs)
      in
      match digits with
      | [] => DNone  (* DP3: '-' with nothing after *)
      | d0 :: drest =>
          if negb (is_digit d0) then DNone  (* DP5: leading non-digit (incl '+', space) *)
          else
            (* DP4: leading zero rule *)
            if ascii_eqb d0 (ascii_of_N 48) (* '0' *)
            then
              match drest with
              | [] =>
                  (* exactly "0" or "-0"; strict grammar: "-0" is NOT a valid integer
                     (it is not the canonical representation of zero). *)
                  if negative then DNone
                  else DSome (DInt 0)
              | _ => DNone  (* "0..." with trailing chars → leading-zero violation *)
              end
            else
              (* DP6: non-zero leading digit — parse all digits *)
              if List.forallb is_digit drest
              then
                (* DP7: apply sign *)
                let magnitude := parse_digits digits 0 in
                let z := if negative then Z.opp magnitude else magnitude in
                (* DP8: range check *)
                if in_range z then DSome (DInt z) else DNone
              else DNone  (* DP5: non-digit in the body *)
      end
  end.

(** [print_digits_fuel fuel n acc]: extract decimal digits of [n : N] into [acc] (LSB-first)
    using [fuel] steps. [fuel] = 20 suffices for all int64 values (at most 20 decimal digits).
    When fuel = 0 or n = 0, returns [acc]. *)
Fixpoint print_digits_fuel (fuel : nat) (n : N) (acc : list ascii) : list ascii :=
  match fuel with
  | O    => acc   (* fuel exhausted (never happens for in-range int64 with fuel=20) *)
  | S f' =>
      let d := (n mod 10)%N in
      let c := ascii_of_N (48 + d) in
      match (n / 10)%N with
      | N0  => c :: acc           (* n < 10: last digit, MSB reached *)
      | n'  => print_digits_fuel f' n' (c :: acc)
      end
  end.

(** [apply_print_int z]: canonical decimal of an in-range DInt; DNone if out of range.
    The print grammar is: optional '-' for negative; digits with no leading zeros; "0" for zero.
    This is the INVERSE of apply_parse_int64's strict grammar.
    Implemented without DecimalString (avoids extracting the Decimal/BinNat/DecimalString modules). *)
Definition apply_print_int (z : Z) : dval :=
  if negb (in_range z) then DNone
  else
    let digits : list ascii :=
      match z with
      | Z0     => [ascii_of_N 48]        (* "0" *)
      | Zpos p =>
          (* print_digits_fuel with fuel=20 (int64_max has 19 digits); result is MSB-first *)
          print_digits_fuel 20 (Npos p) []
      | Zneg p =>
          ascii_of_N 45 :: print_digits_fuel 20 (Npos p) []
      end
    in
    DSome (DBytes digits).

(** [apply_bytes_sub bs offset len]: slice of [bs] starting at [offset] with [len] bytes.
    Returns DSome (DBytes slice) if 0 <= offset, 0 <= len, offset + len <= |bs|; else DNone. *)
Definition apply_bytes_sub (bs : list ascii) (offset len : Z) : dval :=
  let n := Z.of_nat (List.length bs) in
  if Z.ltb offset 0 || Z.ltb len 0 || Z.ltb n (offset + len)
  then DNone
  else
    let drop_n := Z.to_nat offset in
    let take_n := Z.to_nat len in
    let dropped := List.skipn drop_n bs in
    DSome (DBytes (List.firstn take_n dropped)).

(** [to_lower_ascii c]: ASCII case fold, one byte (R12). Bytes 65-90 ('A'-'Z') shift
    +32 to 97-122 ('a'-'z'); EVERY other byte is unchanged — digits, punctuation, NUL,
    and bytes > 127 included (a pure ASCII fold: no locale, no UTF-8). *)
Definition to_lower_ascii (c : ascii) : ascii :=
  let n := N_of_ascii c in
  if (65 <=? n)%N && (n <=? 90)%N then ascii_of_N (n + 32) else c.

(** [to_upper_ascii c]: the inverse direction (R12). Bytes 97-122 ('a'-'z') shift -32
    to 65-90 ('A'-'Z'); every other byte unchanged (same non-letter posture). *)
Definition to_upper_ascii (c : ascii) : ascii :=
  let n := N_of_ascii c in
  if (97 <=? n)%N && (n <=? 122)%N then ascii_of_N (n - 32) else c.

(** [apply_lower_bytes bs] / [apply_upper_bytes bs]: byte-wise map of the fold above
    over the whole byte string (R12, adr-0009 discipline). Total — always a DBytes of
    the SAME length; the option encoding is only used by [apply_prim] for the shape
    mismatch case. *)
Definition apply_lower_bytes (bs : list ascii) : dval :=
  DBytes (List.map to_lower_ascii bs).

Definition apply_upper_bytes (bs : list ascii) : dval :=
  DBytes (List.map to_upper_ascii bs).

(** ** [apply_prim p args]: the TOTAL reference definition of each primitive.
    Arity or shape mismatch → DNone (adr-0009 §Decision 2). *)
Definition apply_prim (p : prim) (args : list dval) : dval :=
  match p, args with
  | PAddChecked,  [DInt a; DInt b]     => apply_add_checked a b
  | PSubChecked,  [DInt a; DInt b]     => apply_sub_checked a b
  | PCmpInt,      [DInt a; DInt b]     => apply_cmp_int a b
  | PEqBytes,     [DBytes a; DBytes b] => DBool (ascii_list_eqb a b)
  | PBytesLen,    [DBytes bs]          => DInt (Z.of_nat (List.length bs))
  | PBytesConcat, [DBytes a; DBytes b] => DBytes (a ++ b)
  | PBytesSub,    [DBytes bs; DInt off; DInt len] => apply_bytes_sub bs off len
  | PParseInt64,  [DBytes bs]          => apply_parse_int64 bs
  | PPrintInt,    [DInt z]             => apply_print_int z
  | PMulChecked,  [DInt a; DInt b]     => apply_mul_checked a b
  | PListLen,     [DList vs]           => DInt (Z.of_nat (List.length vs))
  | PListNth,     [DList vs; DInt i]   => apply_list_nth vs i
  | PDivFloor,    [DInt a; DInt b]     => apply_div_floor a b
  | PLowerBytes,  [DBytes bs]          => apply_lower_bytes bs
  | PUpperBytes,  [DBytes bs]          => apply_upper_bytes bs
  | PListSnoc,    [DList vs; v]        => DList (vs ++ [v])   (* append at the END (R13) *)
  | _, _                               => DNone   (* arity/shape mismatch *)
  end.

(** The result of running a computation: a normal value, or an error that aborted it.
    This is what lets [Bind] short-circuit on [OThrow] (the Error effect). *)
Inductive outcome : Type := ORet (v : dval) | OErr (e : dval).

(** ** Depth-1 patterns for the general [Match] form (adr-0008-general-match).
    Literal patterns bind 0 variables; constructor patterns bind their payloads.

    Binder convention (canonical de Bruijn assignment):
      [match_pat] returns payloads in the order they appear in the pattern.
      The interpreter pushes them onto the environment left-to-right (first payload pushed
      first, last payload pushed last), so de Bruijn 0 = last pushed = last payload.
      Concretely:
        PSome  : binds 1 variable; de Bruijn 0 = the wrapped value.
        PPair  : binds 2 variables; push first then second, so
                   de Bruijn 0 = second component (last pushed),
                   de Bruijn 1 = first component.
      Literal patterns (PUnit/PBool/PInt/PBytes) bind 0 variables: no new binders. *)
Inductive pat : Type :=
| PUnit  : pat
| PBool  : bool -> pat
| PInt   : Z -> pat
| PBytes : list ascii -> pat
| PNone  : pat
| PSome  : pat           (** binds 1: de Bruijn 0 = payload *)
| PPair  : pat           (** binds 2: de Bruijn 0 = second, de Bruijn 1 = first *)
| PTag   : Z -> pat.     (** binds 1: literal tag; de Bruijn 0 = payload (R7, adr-0010) *)

(** [match_pat p d] tests whether [d] matches pattern [p].
    On success it returns [Some payloads] where [payloads] is the list of sub-values
    bound by [p] in the order they appear in the pattern (first component first for PPair).
    The interpreter pushes them in that order, so the last element in [payloads] lands at
    de Bruijn 0. *)
Definition match_pat (p : pat) (d : dval) : option (list dval) :=
  match p, d with
  | PUnit,     DUnit      => Some []
  | PBool b,   DBool b'   => if Bool.eqb b b' then Some [] else None
  | PInt z,    DInt z'    => if Z.eqb z z' then Some [] else None
  | PBytes bs, DBytes bs' => if ascii_list_eqb bs bs' then Some [] else None
  | PNone,     DNone      => Some []
  | PSome,     DSome x    => Some [x]
  | PPair,     DPair a b  => Some [a; b]
  | PTag z,    DTag z' v  => if Z.eqb z z' then Some [v] else None
  | _, _                  => None
  end.

(** Push a list of values onto the environment left-to-right.
    After [push_env vs env], de Bruijn 0 = last element of [vs], which is the last payload
    returned by [match_pat]. *)
Definition push_env (vs : list dval) (env : list dval) : list dval :=
  List.fold_left (fun acc v => v :: acc) vs env.

(** ** Effectful computations. [Bind t1 t2] binds the result of [t1] at de Bruijn 0 in
    [t2]; [Match scrutinee branches default] is the general IR v2 match form:
    first-match-wins over [branches], falling through to [default] on no match.
    [Prim p args] evaluates the [args] as vals and applies the primitive [p] — a pure step,
    Ret-like, yielding the result as a dval (adr-0009-vprim-registry §Decision 1). *)
Inductive tm : Type :=
| Ret     : val -> tm
| Bind    : tm -> tm -> tm
| Perform : op -> list val -> tm
| Match   : val -> list (pat * tm) -> tm -> tm
           (** [Match scrutinee branches default]: evaluate [scrutinee], try each branch
               in order; the first matching branch runs its body with bound payloads pushed
               left-to-right (last payload = de Bruijn 0); [default] runs on no match. *)
| Repeat  : nat -> tm -> tm    (* bounded loop: run [body] [n] times (the report's for_i / fuel recursion) *)
| Prim    : prim -> list val -> tm
           (** [Prim p args]: evaluate each val in [args], apply [apply_prim p], yield result.
               Pure step (no world change); [Bind] sequences the result into the continuation.
               Result is always a dval (may be DNone for mismatch/failure). *)
| Fold    : val -> tm -> tm -> tm.
           (** [Fold lst init body] (R6, adr-0012-list-elimination): the accumulator fold
               bounded by the list. Evaluate [lst]; run [init] for the starting
               accumulator; per element LEFT TO RIGHT run [body] with the environment
               extended via [push_env [elem; acc]] (acc = de Bruijn 0, element = de
               Bruijn 1); [body]'s result is the next accumulator; the final accumulator
               is the result. [OErr] from [init] or any iteration short-circuits; the
               world threads. Non-[DList] scrutinee: the fold is EMPTY (result = [init]'s
               result — [init]'s effects still happen exactly once). *)

(** ** Pure-value evaluation in a de Bruijn environment. Total: out-of-scope vars and
    type errors yield [Dstuck]. *)
Fixpoint eval_val (env : list dval) (v : val) : dval :=
  match v with
  | VVar n   => nth n env Dstuck
  | VUnit    => DUnit
  | VBool b  => DBool b
  | VInt z   => DInt z
  | VNone    => DNone
  | VSome a  => DSome (eval_val env a)
  | VPair a b => DPair (eval_val env a) (eval_val env b)
  | VZero    => DInt 0
  | VSucc a  => match eval_val env a with
                | DInt z => DInt (Z.succ z)
                | _      => Dstuck
                end
  | VBytes bs => DBytes bs
  | VTag z a  => DTag z (eval_val env a)
  | VList vs  =>
      (* Nested fix over the value list — same technique as [run]'s Match branch-list
         (adr-0008): each element of [vs] is a strict sub-component of [VList vs], which
         is a strict sub-component of [v], so the outer fixpoint stays structurally
         guarded even though the recursion goes through [List.map]-shaped code. *)
      DList ((fix eval_list (xs : list val) : list dval :=
                match xs with
                | []       => []
                | x :: xs' => eval_val env x :: eval_list xs'
                end) vs)
  end.

(** ** Store state (R4, adr-0011): each binding carries the value and an OPTIONAL absolute
    deadline in ms. The cache stays a plain [dval] map (no deadlines) — memoization has no
    expiry semantics and is observationally invisible anyway. *)
Definition entry : Type := (dval * option Z)%type.
Definition state : Type := M.t entry.
Definition memo  : Type := M.t dval.

Definition opt_to_dval (o : option dval) : dval :=
  match o with Some v => DSome v | None => DNone end.

(** ** Liveness — the ONE rule (adr-0011 §Decision 3, oracle-validated at the boundary:
    12,500-case prediction-vs-oracle run, 0 mismatches — alive AT the exact deadline,
    dead at deadline+1ms). A binding [(v, Some d)] is live iff [now <= d]; [(v, None)]
    is always live. The mutant that uses [<] (dead AT the deadline) is observably
    rejected in theories/TimeStore.v. *)
Definition live (now : Z) (e : entry) : bool :=
  match snd e with
  | None   => true
  | Some d => now <=? d
  end.

(** The LIVE view of a key: expired bindings are semantically absent for every op. *)
Definition find_live (now : Z) (k : string) (s : state) : option entry :=
  match M.find k s with
  | Some e => if live now e then Some e else None
  | None   => None
  end.

(** ** The [world]: ALL ambient effect state bundled into one record, so adding an effect
    adds a FIELD here rather than another parameter to [run] (the refactor that motivated
    the Trace iteration). [kv] is the expiring store, [ctx] the read-only Env context,
    [now_ms] the run's single instant (R5: immutable within a run — a program executes
    atomically at one instant; the harness advances the clock BETWEEN runs, adr-0011
    §Decision 1), [trace] the Trace log stored newest-first (reversed by [observe]),
    [journal] the R9 append-only Journal, also newest-first (reversed by [observe_full])
    — write-only: [OJournal] appends [(now_ms, v)] and NO op reads it (adr-0013). *)
Record world : Type := mkWorld {
  kv      : state;
  ctx     : dval;
  now_ms  : Z;          (* the run's instant; read by ONow and by store liveness *)
  trace   : list dval;
  cache   : memo;       (* memo store; deliberately NOT exposed by [observe] *)
  journal : list (Z * dval);  (* R9 append-only log, newest-first (adr-0013) *)
}.

Definition set_kv    (w : world) (m : state)     : world :=
  mkWorld m w.(ctx) w.(now_ms) w.(trace) w.(cache) w.(journal).
Definition set_trace (w : world) (l : list dval) : world :=
  mkWorld w.(kv) w.(ctx) w.(now_ms) l w.(cache) w.(journal).
Definition set_cache (w : world) (c : memo)      : world :=
  mkWorld w.(kv) w.(ctx) w.(now_ms) w.(trace) c w.(journal).
Definition set_journal (w : world) (l : list (Z * dval)) : world :=
  mkWorld w.(kv) w.(ctx) w.(now_ms) w.(trace) w.(cache) l.

(** ** Pure store handler over the map: the reference semantics of the store operations
    (adr-0011 §Decision 2 — the op table, verbatim):
      OGet         [k]     -> DNone | DSome v                       (live bindings only)
      OPut         [k; v]  -> DUnit    stores v and CLEARS any deadline
      ODelete      [k]     -> DBool    true iff a LIVE binding was removed
      OGetDeadline [k]     -> DNone (no live k) | DSome DNone (live, no deadline)
                              | DSome (DSome (DInt d))
      OSetDeadline [k; DNone | DSome (DInt d)] -> DBool  true iff a live binding modified
    Keys are byte strings ([DBytes]); arity/shape mismatch yields [Dstuck] (the existing
    malformed-Perform-args convention). Whether an expired binding is physically removed
    is unobservable ([ODelete] removes it; reads leave it) — lazy deletion freedom. *)
Definition handle_store (now : Z) (o : op) (args : list dval) (s : state) : dval * state :=
  match o, args with
  | OGet, [DBytes kb] =>
      (match find_live now (string_of_list_ascii kb) s with
       | Some (v, _) => DSome v
       | None        => DNone
       end, s)
  | OPut, [DBytes kb; v] =>
      (DUnit, M.add (string_of_list_ascii kb) (v, None) s)
  | ODelete, [DBytes kb] =>
      let k := string_of_list_ascii kb in
      (match find_live now k s with
       | Some _ => DBool true
       | None   => DBool false
       end, M.remove k s)
  | OGetDeadline, [DBytes kb] =>
      (match find_live now (string_of_list_ascii kb) s with
       | Some (_, None)   => DSome DNone
       | Some (_, Some d) => DSome (DSome (DInt d))
       | None             => DNone
       end, s)
  | OSetDeadline, [DBytes kb; DNone] =>
      let k := string_of_list_ascii kb in
      match find_live now k s with
      | Some (v, _) => (DBool true, M.add k (v, None) s)
      | None        => (DBool false, s)
      end
  | OSetDeadline, [DBytes kb; DSome (DInt d)] =>
      let k := string_of_list_ascii kb in
      match find_live now k s with
      | Some (v, _) => (DBool true, M.add k (v, Some d) s)
      | None        => (DBool false, s)
      end
  | _, _ => (Dstuck, s)
  end.

(** ** The reference interpreter, threading one [world]. Structurally recursive on [t],
    hence total. [Bind] short-circuits on abort ([OErr]); [OThrow e] aborts; [OAsk] reads
    [ctx]; [OTrace v] appends [v] to the log; KV ops update [kv]. *)
Fixpoint run (env : list dval) (t : tm) (w : world) : outcome * world :=
  match t with
  | Ret v        => (ORet (eval_val env v), w)
  | Bind t1 t2   =>
      match run env t1 w with
      | (ORet x, w') => run (x :: env) t2 w'
      | (OErr e, w') => (OErr e, w')   (* abort: the continuation does not run *)
      end
  | Perform o args =>
      let vs := map (eval_val env) args in
      match o with
      | OThrow => (OErr (nth 0 vs Dstuck), w)
      | OAsk   => (ORet w.(ctx), w)
      | ONow   => (ORet (DInt w.(now_ms)), w)   (* R5: the run's single instant *)
      | OTrace => match vs with
                  | [v] => (ORet DUnit, set_trace w (v :: w.(trace)))
                  | _   => (ORet Dstuck, w)
                  end
      | OCacheGet => match vs with
                     | [DBytes kb] =>
                         (ORet (opt_to_dval (M.find (string_of_list_ascii kb) w.(cache))), w)
                     | _        => (ORet Dstuck, w)
                     end
      | OCachePut => match vs with
                     | [DBytes kb; v] =>
                         (ORet DUnit, set_cache w (M.add (string_of_list_ascii kb) v w.(cache)))
                     | _           => (ORet Dstuck, w)
                     end
      | OJournal => match vs with
                    | [v] => (* R9 (adr-0013): append (run instant, payload), newest-first;
                                the result is DUnit — the journal is write-only. *)
                        (ORet DUnit, set_journal w ((w.(now_ms), v) :: w.(journal)))
                    | _   => (ORet Dstuck, w)
                    end
      | _      => let '(r, s') := handle_store w.(now_ms) o vs w.(kv) in (ORet r, set_kv w s')
      end
  | Match scrut branches default =>
      let d := eval_val env scrut in
      (* Nested fix over the branch list — each branch body is a structural sub-component
         of the [Match] constructor, so the outer fixpoint stays structurally guarded. *)
      (fix try_branches (bs : list (pat * tm)) {struct bs} : outcome * world :=
         match bs with
         | []           => run env default w    (* no branch matched: run the default *)
         | (p, body) :: rest =>
             match match_pat p d with
             | Some payloads =>
                 (* Push payloads left-to-right; last payload = de Bruijn 0. *)
                 run (push_env payloads env) body w
             | None => try_branches rest        (* pattern mismatch: try next branch *)
             end
         end) branches
  | Repeat n body =>
      (* run [body] [n] times, threading the world; an abort stops the loop. The inner
         [loop] recurses on the fuel [m]; the calls to [run env body] are on a strict
         subterm of [Repeat n body], so the outer fixpoint stays structurally guarded. *)
      (fix loop (m : nat) (w0 : world) {struct m} : outcome * world :=
         match m with
         | O    => (ORet DUnit, w0)
         | S m' => match run env body w0 with
                   | (ORet _, w1) => loop m' w1
                   | (OErr e, w1) => (OErr e, w1)
                   end
         end) n w
  | Prim p args =>
      (* Evaluate each argument val in the current environment, apply the prim reference
         definition, return the result — world is unchanged (pure step). *)
      let vs := map (eval_val env) args in
      (ORet (apply_prim p vs), w)
  | Fold lst init body =>
      (* R6 (adr-0012): evaluate the scrutinee (pure), run [init] once for the starting
         accumulator, then iterate the elements LEFT TO RIGHT. The inner [fold_elems]
         recurses structurally on the element list [xs] (the bound comes from the data,
         which is finite — no fuel); the calls to [run … body] are on a strict subterm of
         [Fold lst init body], so the outer fixpoint stays structurally guarded (the
         Repeat/Match nested-fix technique). An [OErr] from [init] or any iteration
         short-circuits; the world threads through iterations. A non-[DList] scrutinee
         yields [init]'s result (empty fold — adr-0012 §Decision 2). *)
      let d := eval_val env lst in
      match run env init w with
      | (OErr e, w') => (OErr e, w')     (* init aborted: the fold never starts *)
      | (ORet acc0, w') =>
          match d with
          | DList vs =>
              (fix fold_elems (xs : list dval) (acc : dval) (w0 : world) {struct xs}
                 : outcome * world :=
                 match xs with
                 | []       => (ORet acc, w0)
                 | x :: xs' =>
                     (* push_env [elem; acc]: acc pushed last = de Bruijn 0, elem = 1. *)
                     match run (push_env [x; acc] env) body w0 with
                     | (ORet acc', w1) => fold_elems xs' acc' w1
                     | (OErr e, w1)    => (OErr e, w1)   (* abort mid-fold *)
                     end
                 end) vs acc0 w'
          | _ => (ORet acc0, w')          (* non-DList: empty fold, init's result *)
          end
      end
  end.

(** Initial world: empty store, the given [c] context, the run's instant [now], empty
    trace, empty cache, empty journal. *)
Definition init_world (c : dval) (now : Z) : world :=
  mkWorld (M.empty entry) c now [] (M.empty dval) [].

Definition run_top (c : dval) (now : Z) (t : tm) : outcome * world :=
  run [] t (init_world c now).

(** The LIVE bindings of a store at instant [now]: expired bindings are filtered out —
    they are semantically absent from the observable too (adr-0011 §Decision 3). Each
    surviving binding keeps its (value, optional deadline) entry. *)
Definition live_elements (now : Z) (s : state) : list (string * entry) :=
  List.filter (fun ke => live now (snd ke)) (M.elements s).

(** The observable: outcome + sorted LIVE key/entry bindings + the chronological trace. *)
Definition observe (c : dval) (now : Z) (t : tm)
  : outcome * list (string * entry) * list dval :=
  let '(r, w) := run_top c now t in (r, live_elements now w.(kv), rev w.(trace)).

(** Like [observe] but from a custom initial store state [s] (and context [c], instant
    [now]); the single entry point the differential tests use (they seed a non-empty
    state, deadlines included). R9 (adr-0013): the observable gains the JOURNAL, reversed
    to chronological order — exactly like the trace. *)
Definition observe_full (c : dval) (now : Z) (s : state) (t : tm)
  : outcome * list (string * entry) * list dval * list (Z * dval) :=
  let '(r, w) := run [] t (mkWorld s c now [] (M.empty dval) []) in
  (r, live_elements now w.(kv), rev w.(trace), rev w.(journal)).

(** ** The slice-1 example program: increment the [option]-valued counter at a key.
    [incr_at k] = get k; if absent put (succ zero)=1 else put (succ x).
    Migrated from MatchOpt to Match (adr-0008 §Decision 5); keys are decimal byte
    strings since R4 (adr-0011 §Decision 5). *)
Definition incr_at (k : list ascii) : tm :=
  Bind (Perform OGet [VBytes k])
       (Match (VVar 0)
          [(PNone, Perform OPut [VBytes k; VSucc VZero]);
           (PSome, Perform OPut [VBytes k; VSucc (VVar 0)])]
          (Perform OPut [VBytes k; VSucc VZero])).

(** The closed spike term used to validate the extraction->codegen bridge (Step 1).
    Key "7" = the decimal bytes of the original slice-1 integer key 7. *)
Definition key7 : list ascii := list_ascii_of_string "7".
Definition prog0 : tm := incr_at key7.
