(** * EffIR — first-order effect IR (v2, R3: VPrim primitive registry) and its reference semantics.

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
    definition; [run] handles the [Prim] case by evaluating args then applying [apply_prim]. *)

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

(** A Z-keyed finite map is the reference KV state. FMapAVL gives sorted [elements],
    which is exactly the order-independent observable the differential test compares
    against the OCaml Hashtbl (kb/spec/reference-semantics.md). *)
Module M := FMapAVL.Make(Z_as_OT).

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
| VBytes  : list ascii -> val.

(** ** Effect operations: KV (Get/Put/Delete), [OThrow] (Error), [OAsk] (Env), [OTrace]
    (Trace), and [OCacheGet]/[OCachePut] (Cache — a memo store kept OUT of [observe], so it
    is observationally invisible) — kb/spec/effect-signatures.md. *)
Inductive op : Type :=
  | OGet | OPut | ODelete | OThrow | OAsk | OTrace | OCacheGet | OCachePut.

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
| PPrintInt.    (** DInt z -> DSome (DBytes decimal) if in-range, DNone if not *)

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
| PPair  : pat.          (** binds 2: de Bruijn 0 = second, de Bruijn 1 = first *)

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
| Prim    : prim -> list val -> tm.
           (** [Prim p args]: evaluate each val in [args], apply [apply_prim p], yield result.
               Pure step (no world change); [Bind] sequences the result into the continuation.
               Result is always a dval (may be DNone for mismatch/failure). *)

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
  end.

Definition state : Type := M.t dval.

Definition opt_to_dval (o : option dval) : dval :=
  match o with Some v => DSome v | None => DNone end.

(** ** The [world]: ALL ambient effect state bundled into one record, so adding an effect
    adds a FIELD here rather than another parameter to [run] (the refactor that motivated
    the Trace iteration). [kv] is the KV map, [ctx] the read-only Env context, [trace] the
    Trace log stored newest-first (reversed to chronological by [observe]). *)
Record world : Type := mkWorld {
  kv    : state;
  ctx   : dval;
  trace : list dval;
  cache : state;       (* memo store; deliberately NOT exposed by [observe] *)
}.

Definition set_kv    (w : world) (m : state)     : world := mkWorld m w.(ctx) w.(trace) w.(cache).
Definition set_trace (w : world) (l : list dval) : world := mkWorld w.(kv) w.(ctx) l w.(cache).
Definition set_cache (w : world) (c : state)     : world := mkWorld w.(kv) w.(ctx) w.(trace) c.

(** ** Pure KV handler over the map: the reference semantics of the KV operations. *)
Definition handle_kv (o : op) (args : list dval) (s : state) : dval * state :=
  match o, args with
  | OGet,    [DInt k]        => (opt_to_dval (M.find k s), s)
  | OPut,    [DInt k; v]     => (DUnit, M.add k v s)
  | ODelete, [DInt k]        => (DUnit, M.remove k s)
  | _, _                     => (Dstuck, s)
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
      | OTrace => match vs with
                  | [v] => (ORet DUnit, set_trace w (v :: w.(trace)))
                  | _   => (ORet Dstuck, w)
                  end
      | OCacheGet => match vs with
                     | [DInt k] => (ORet (opt_to_dval (M.find k w.(cache))), w)
                     | _        => (ORet Dstuck, w)
                     end
      | OCachePut => match vs with
                     | [DInt k; v] => (ORet DUnit, set_cache w (M.add k v w.(cache)))
                     | _           => (ORet Dstuck, w)
                     end
      | _      => let '(r, s') := handle_kv o vs w.(kv) in (ORet r, set_kv w s')
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
  end.

(** Initial world: empty store, the given [c] context, empty trace, empty cache. *)
Definition init_world (c : dval) : world := mkWorld (M.empty dval) c [] (M.empty dval).

Definition run_top (c : dval) (t : tm) : outcome * world := run [] t (init_world c).

(** The observable: outcome + sorted key/value bindings + the trace in chronological order. *)
Definition observe (c : dval) (t : tm) : outcome * list (Z * dval) * list dval :=
  let '(r, w) := run_top c t in (r, M.elements w.(kv), rev w.(trace)).

(** Like [observe] but from a custom initial KV state [s] (and context [c]); the single
    entry point the differential tests use (they seed a non-empty state). *)
Definition observe_full (c : dval) (s : state) (t : tm)
  : outcome * list (Z * dval) * list dval :=
  let '(r, w) := run [] t (mkWorld s c [] (M.empty dval)) in (r, M.elements w.(kv), rev w.(trace)).

(** ** The slice-1 example program: increment the [option]-valued counter at a key.
    [incr_at k] = get k; if absent put (succ zero)=1 else put (succ x).
    Migrated from MatchOpt to Match (adr-0008 §Decision 5). *)
Definition incr_at (k : Z) : tm :=
  Bind (Perform OGet [VInt k])
       (Match (VVar 0)
          [(PNone, Perform OPut [VInt k; VSucc VZero]);
           (PSome, Perform OPut [VInt k; VSucc (VVar 0)])]
          (Perform OPut [VInt k; VSucc VZero])).

(** The closed spike term used to validate the extraction->codegen bridge (Step 1). *)
Definition prog0 : tm := incr_at 7.
