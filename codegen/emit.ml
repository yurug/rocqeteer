(** Emit — the rocqeteer codegen LIBRARY core (R10 v1 split, adr-0014-wf-checker: the
    emission core + the wf gate live here under (public_name rocqeteer.codegen); the
    rocqeteer-codegen executable is a thin driver over [emit_programs], and consumers
    link this library to lower THEIR extracted [all_programs] into their generated/
    file).

    IR v2 R9 (Journal effect, adr-0013-journal-effect — [OJournal]
    lowers to [Journal.append]; the R9 prim [PDivFloor] lowers to
    [Prims.prim_div_floor]): lower an
    extracted EffIR [tm] to direct-style OCaml 5. R4+R5 (adr-0011) made [emit_key] a
    BYTES emitter ([VBytes] key literals -> escaped [Bytes.of_string] literals; a [VVar]
    key extracts the payload of an [Rval.Bytes]), re-shaped [OGet]/[OPut]/[ODelete] to
    the store signatures, and added [OGetDeadline]/[OSetDeadline]/[ONow]. R6 adds the
    [Fold] lowering (-> a native [List.fold_left], adr-0012 §Decision 5 — the second
    binder-introducing construct after [Match]; see the db0/db1 comment at the [Fold]
    case) and the three R6 prims ([PMulChecked]/[PListLen]/[PListNth]).

    The monad is ERASED by construction: [Bind] -> [let], [Perform] -> a [Kv.*] call,
    [Match] -> chained match/if (adr-0008-general-match §Decision 4). No [Bind]/free-monad
    constructor survives into the output (property P3). Out-of-fragment input fails loudly
    rather than emitting unsound code (kb/spec/codegen.md, kb/spec/error-taxonomy.md).

    Values are typed as [Rval.t] at effect boundaries (IR v2 milestone 1); every store op
    returns [Rval.t] (get: None/Some, put: Unit, delete: Bool, get_deadline: the
    nested-option encoding, set_deadline: Bool), so heterogeneous Match branches stay
    well-typed. When generated code consumes a value at a narrower type (e.g. [VSucc] on
    a bound variable, or a [VVar] in key position), it emits a match whose fallback raises
    [Rval.Stuck], mirroring the reference interpreter's [Dstuck] sentinel. *)

open Ref_extracted.EffIR

module BinNums = Ref_extracted.BinNums

exception Codegen_error of string

(* The name of the next binder is its de Bruijn DEPTH (= current environment length), so
   names are v0, v1, ... by scope depth: deterministic (byte-stable output, P4/NF5) with no
   global mutable state, and they reset naturally per program (kb/conventions/code-style.md). *)
let bind_name (env : string list) : string = "v" ^ string_of_int (List.length env)

(* A coq_Z literal becomes an exact zarith value via its decimal string (any size). *)
let emit_z (z : BinNums.coq_Z) : string =
  Printf.sprintf "(Z.of_string \"%s\")" (Z.to_string (Coqconv.z_of_coqz z))

(* Emit a deterministically escaped bytes-literal body from an ascii list: printable
   ASCII (0x20–0x7E, minus backslash and double-quote) as-is; all other bytes as \xNN.
   Binary-safe, byte-stable output (property P4/NF5) regardless of content. *)
let emit_bytes_literal bs =
  let chars = List.map Coqconv.char_of_ascii bs in
  let buf = Buffer.create (List.length chars * 2) in
  List.iter (fun c ->
    let n = Char.code c in
    if n >= 0x20 && n <= 0x7E && c <> '"' && c <> '\\' then
      Buffer.add_char buf c
    else (
      Buffer.add_string buf "\\x";
      Buffer.add_string buf (Printf.sprintf "%02x" n))
  ) chars;
  Buffer.contents buf

(* [emit_key] emits a [bytes] expression for a store/Cache key argument (R4, adr-0011:
   keys are byte strings). [VBytes] is the key-literal form; a [VVar] key extracts the
   payload of an [Rval.Bytes], raising [Rval.Stuck] on ill-typed values (mirroring the
   reference [Dstuck] on a non-bytes key). *)
let emit_key (env : string list) (v : coq_val) : string =
  match v with
  | VBytes bs ->
      Printf.sprintf "(Bytes.of_string \"%s\")"
        (emit_bytes_literal (Coqconv.list_of_coq bs))
  | VVar n  -> (
      match List.nth_opt env (Coqconv.int_of_nat n) with
      | Some name ->
          Printf.sprintf "(match %s with Rval.Bytes _b -> _b | _ -> raise Rval.Stuck)" name
      | None -> raise (Codegen_error "VVar index out of scope (key)"))
  | _ -> raise (Codegen_error "non-bytes value used in key position")

(* [emit_val] emits a [Rval.t] expression.
   [VSucc] requires the inner value to be [Rval.Int]; the match raises [Rval.Stuck] on
   ill-typed values, mirroring the reference [Dstuck] on impossible cases. *)
let rec emit_val (env : string list) (v : coq_val) : string =
  match v with
  | VVar n -> (
      match List.nth_opt env (Coqconv.int_of_nat n) with
      | Some name -> name
      | None -> raise (Codegen_error "VVar index out of scope"))
  | VUnit   -> "Rval.Unit"
  | VBool b -> if Coqconv.bool_of_coq b then "(Rval.Bool true)" else "(Rval.Bool false)"
  | VInt z  -> Printf.sprintf "(Rval.Int %s)" (emit_z z)
  | VNone   -> "Rval.None"
  | VSome a -> Printf.sprintf "(Rval.Some %s)" (emit_val env a)
  | VPair (a, b) ->
      Printf.sprintf "(Rval.Pair (%s, %s))" (emit_val env a) (emit_val env b)
  | VZero   -> "(Rval.Int Z.zero)"
  | VSucc a ->
      (* The inner value must be [Rval.Int]; emit a match whose fallback raises [Rval.Stuck],
         mirroring the reference interpreter's [Dstuck] on ill-typed VSucc application. *)
      Printf.sprintf
        "(match %s with Rval.Int _z -> Rval.Int (Z.succ _z) | _ -> raise Rval.Stuck)"
        (emit_val env a)
  | VBytes bs ->
      (* Emit [Rval.Bytes (Bytes.of_string "...")].  Each byte is escaped deterministically:
         printable ASCII (0x20–0x7E) except backslash and double-quote are emitted as-is;
         all other bytes use \xNN (two hex digits).  This guarantees binary-safe, byte-stable
         output (property P4/NF5) regardless of the byte content. *)
      let chars =
        Coqconv.list_of_coq bs
        |> List.map Coqconv.char_of_ascii
      in
      let buf = Buffer.create (List.length chars * 2) in
      List.iter (fun c ->
        let n = Char.code c in
        if n >= 0x20 && n <= 0x7E && c <> '"' && c <> '\\' then
          Buffer.add_char buf c
        else (
          Buffer.add_string buf "\\x";
          Buffer.add_string buf (Printf.sprintf "%02x" n))
      ) chars;
      Printf.sprintf "(Rval.Bytes (Bytes.of_string \"%s\"))" (Buffer.contents buf)
  | VTag (z, a) ->
      (* R7 (adr-0010-structured-values): a tagged sum injection. *)
      Printf.sprintf "(Rval.Tag (%s, %s))" (emit_z z) (emit_val env a)
  | VList vs ->
      (* R7 (adr-0010-structured-values): a finite sequence; [] for the empty list. *)
      let items = Coqconv.list_of_coq vs |> List.map (emit_val env) in
      Printf.sprintf "(Rval.List [%s])" (String.concat "; " items)

(* Store/Time/etc. operations lower to the curried public wrappers
   (kb/spec/effect-signatures.md, Resolution 7). Wrong arity is a codegen error, not a
   silent cast. Key arguments use [emit_key] (bytes); value arguments use [emit_val]
   (Rval.t); [OSetDeadline]'s deadline argument is a val (VNone | VSome (VInt d)) and
   goes through [emit_val] unchanged (adr-0011 — no new val constructors). *)
let emit_perform (env : string list) (o : op) (args : coq_val list) : string =
  match o, args with
  | OGet,    [k]     -> Printf.sprintf "(Kv.get %s)" (emit_key env k)
  | OPut,    [k; v]  -> Printf.sprintf "(Kv.put %s %s)" (emit_key env k) (emit_val env v)
  | ODelete, [k]     -> Printf.sprintf "(Kv.delete %s)" (emit_key env k)
  | OGetDeadline, [k] -> Printf.sprintf "(Kv.get_deadline %s)" (emit_key env k)
  | OSetDeadline, [k; d] ->
      Printf.sprintf "(Kv.set_deadline %s %s)" (emit_key env k) (emit_val env d)
  | ONow,    []      -> "(Time.now ())"
  | OThrow,  [e]     -> Printf.sprintf "(Err.throw %s)" (emit_val env e)
  | OAsk,    []      -> "(Env.ask ())"
  | OTrace,  [v]     -> Printf.sprintf "(Trace.emit %s)" (emit_val env v)
  | OCacheGet, [k]   -> Printf.sprintf "(Cache.get %s)" (emit_key env k)
  | OCachePut, [k;v] -> Printf.sprintf "(Cache.put %s %s)" (emit_key env k) (emit_val env v)
  | OJournal, [v]    -> Printf.sprintf "(Journal.append %s)" (emit_val env v)
  (* C3 (adr-0017): the file family — path through emit_key (bytes); fd/maxlen/mode/
     payload through emit_val (the wrappers mirror handle_file's shape checks). *)
  | OOpen,   [p; m]  -> Printf.sprintf "(Fileio.open_ %s %s)" (emit_key env p) (emit_val env m)
  | ORead,   [f; n]  -> Printf.sprintf "(Fileio.read %s %s)" (emit_val env f) (emit_val env n)
  | OFWrite, [f; b]  -> Printf.sprintf "(Fileio.write %s %s)" (emit_val env f) (emit_val env b)
  | OClose,  [f]     -> Printf.sprintf "(Fileio.close_ %s)" (emit_val env f)
  (* C4 (adr-0018): the socket family *)
  | OAccept, []      -> "(Sockio.accept ())"
  | ORecv,   [c; n]  -> Printf.sprintf "(Sockio.recv %s %s)" (emit_val env c) (emit_val env n)
  | OSend,   [c; b]  -> Printf.sprintf "(Sockio.send %s %s)" (emit_val env c) (emit_val env b)
  | OCloseConn, [c]  -> Printf.sprintf "(Sockio.close_conn %s)" (emit_val env c)
  | _ -> raise (Codegen_error "effect operation applied at the wrong arity")

(* [emit_branch] compiles one branch (adr-0008 §Decision 4 chaining scheme).
   For literal patterns (PBytes, PUnit, PBool, PInt): emit an if-then-else equality guard.
   For constructor patterns (PNone, PSome, PPair): emit an OCaml match with [| _ -> next].
   [scrut_name] is the already-evaluated scrutinee variable; [next] is the fallback string.

   De Bruijn binder convention for PPair (adr-0008):
     match_pat returns [fst; snd]; push_env pushes left-to-right, so last pushed = db0 = snd.
     The codegen mirrors this: name_fst = bind_name env (depth d), name_snd = bind_name (env+1)
     (depth d+1). The extended env is [name_snd; name_fst; ...env...], so db0 = name_snd (snd
     component) and db1 = name_fst (first component). *)
let rec emit_branch (env : string list) (scrut_name : string) (p : pat) (body : tm) (next : string) : string =
  match p with
  | PBytes bs ->
      let lit = emit_bytes_literal (Coqconv.list_of_coq bs) in
      Printf.sprintf "(if Rval.equal %s (Rval.Bytes (Bytes.of_string \"%s\")) then %s else %s)"
        scrut_name lit (emit_tm env body) next
  | PUnit ->
      Printf.sprintf "(if Rval.equal %s Rval.Unit then %s else %s)"
        scrut_name (emit_tm env body) next
  | PBool b ->
      let blit = if Coqconv.bool_of_coq b then "true" else "false" in
      Printf.sprintf "(if Rval.equal %s (Rval.Bool %s) then %s else %s)"
        scrut_name blit (emit_tm env body) next
  | PInt z ->
      Printf.sprintf "(if Rval.equal %s (Rval.Int %s) then %s else %s)"
        scrut_name (emit_z z) (emit_tm env body) next
  | PNone ->
      Printf.sprintf "(match %s with Rval.None -> %s | _ -> %s)"
        scrut_name (emit_tm env body) next
  | PSome ->
      let name = bind_name env in
      Printf.sprintf "(match %s with Rval.Some %s -> %s | _ -> %s)"
        scrut_name name (emit_tm (name :: env) body) next
  | PPair ->
      let name_fst = bind_name env in               (* = db1 after both are pushed *)
      let name_snd = bind_name (name_fst :: env) in (* = db0 (last pushed) *)
      let env' = name_snd :: name_fst :: env in
      Printf.sprintf "(match %s with Rval.Pair (%s, %s) -> %s | _ -> %s)"
        scrut_name name_fst name_snd (emit_tm env' body) next
  | PTag z ->
      (* R7 (adr-0010-structured-values): literal-tag match, binds 1 payload at db0
         (same binder convention as PSome). The tag guard uses a fixed local name "_t":
         it never escapes this single match arm, so it cannot collide across branches. *)
      let name = bind_name env in
      Printf.sprintf
        "(match %s with Rval.Tag (_t, %s) when Z.equal _t %s -> %s | _ -> %s)"
        scrut_name name (emit_z z) (emit_tm (name :: env) body) next

(* [emit_prim p args] emits the direct-style call to the registered realizer for prim [p].
   Each prim maps to exactly one [Prims.prim_<name>] symbol (adr-0009 §Decision 5).
   Arity is fixed per prim; wrong arity is a codegen error. *)
and emit_prim (env : string list) (p : prim) (args : coq_val list) : string =
  match p, args with
  | PAddChecked,  [a; b]    -> Printf.sprintf "(Prims.prim_add_checked %s %s)"
                                  (emit_val env a) (emit_val env b)
  | PSubChecked,  [a; b]    -> Printf.sprintf "(Prims.prim_sub_checked %s %s)"
                                  (emit_val env a) (emit_val env b)
  | PCmpInt,      [a; b]    -> Printf.sprintf "(Prims.prim_cmp_int %s %s)"
                                  (emit_val env a) (emit_val env b)
  | PEqBytes,     [a; b]    -> Printf.sprintf "(Prims.prim_eq_bytes %s %s)"
                                  (emit_val env a) (emit_val env b)
  | PBytesLen,    [a]       -> Printf.sprintf "(Prims.prim_bytes_len %s)"
                                  (emit_val env a)
  | PBytesConcat, [a; b]    -> Printf.sprintf "(Prims.prim_bytes_concat %s %s)"
                                  (emit_val env a) (emit_val env b)
  | PBytesSub,    [a; b; c] -> Printf.sprintf "(Prims.prim_bytes_sub %s %s %s)"
                                  (emit_val env a) (emit_val env b) (emit_val env c)
  | PParseInt64,  [a]       -> Printf.sprintf "(Prims.prim_parse_int64 %s)"
                                  (emit_val env a)
  | PPrintInt,    [a]       -> Printf.sprintf "(Prims.prim_print_int %s)"
                                  (emit_val env a)
  | PMulChecked,  [a; b]    -> Printf.sprintf "(Prims.prim_mul_checked %s %s)"
                                  (emit_val env a) (emit_val env b)
  | PListLen,     [a]       -> Printf.sprintf "(Prims.prim_list_len %s)"
                                  (emit_val env a)
  | PListNth,     [a; b]    -> Printf.sprintf "(Prims.prim_list_nth %s %s)"
                                  (emit_val env a) (emit_val env b)
  | PDivFloor,    [a; b]    -> Printf.sprintf "(Prims.prim_div_floor %s %s)"
                                  (emit_val env a) (emit_val env b)
  | PLowerBytes,  [a]       -> Printf.sprintf "(Prims.prim_lower_bytes %s)"
                                  (emit_val env a)
  | PUpperBytes,  [a]       -> Printf.sprintf "(Prims.prim_upper_bytes %s)"
                                  (emit_val env a)
  | PListSnoc,    [a; b]    -> Printf.sprintf "(Prims.prim_list_snoc %s %s)"
                                  (emit_val env a) (emit_val env b)
  | PFindSub,     [a; b]    -> Printf.sprintf "(Prims.prim_find_sub %s %s)"
                                 (emit_val env a) (emit_val env b)
  | _ -> raise (Codegen_error "Prim applied at wrong arity")

and emit_tm (env : string list) (t : tm) : string =
  match t with
  | Ret v -> emit_val env v
  | Bind (t1, t2) ->
      let name = bind_name env in
      Printf.sprintf "(let %s = %s in %s)" name (emit_tm env t1)
        (emit_tm (name :: env) t2)
  | Perform (o, args) -> emit_perform env o (Coqconv.list_of_coq args)
  | Match (scrut, branches, default) ->
      (* Branch-by-branch chaining (adr-0008 §Decision 4):
         each branch compiles to a match/if with the next branch as fallback;
         the chain ends at the default arm. Bind the scrutinee to a fresh name once
         so it is evaluated exactly once even if referenced by many branches. *)
      let scrut_name = "_s" ^ string_of_int (List.length env) in
      let default_str = emit_tm env default in
      let branch_list = Coqconv.list_of_coq branches in
      (* Build the chain right-to-left: fold from the end so the first branch wraps last. *)
      let chain =
        List.fold_right
          (fun br next_str ->
             match br with
             | Ref_extracted.Datatypes.Coq_pair (p, body) ->
                 emit_branch env scrut_name p body next_str)
          branch_list
          default_str
      in
      Printf.sprintf "(let %s = %s in %s)" scrut_name (emit_val env scrut) chain
  | Repeat (n, body) ->
      (* bounded loop -> a native for-loop; the body runs n times for its effects *)
      Printf.sprintf "(for _i = 1 to %d do ignore (%s) done)" (Coqconv.int_of_nat n)
        (emit_tm env body)
  | Prim (p, args) ->
      (* Prim step: evaluate args as vals, call the registered realizer (adr-0009 §5). *)
      emit_prim env p (Coqconv.list_of_coq args)
  | Fold (lst, init, body) ->
      (* R6 (adr-0012 §Decision 5): Fold -> a native List.fold_left.

         de Bruijn -> OCaml binder mapping. The reference extends the body env via
         push_env [elem; acc]: elem pushed FIRST, acc pushed LAST, so
           db0 = acc   (last pushed)
           db1 = elem
         The codegen env is a list where index n = de Bruijn n, hence
           env' = name_acc :: name_elem :: env.
         Binder names follow the PPair fresh-name discipline: name_elem = bind_name env
         (depth d), name_acc = bind_name (name_elem :: env) (depth d+1). In the emitted
         [fun name_acc name_elem -> BODY], List.fold_left passes the ACCUMULATOR first
         and the ELEMENT second — matching name_acc = db0, name_elem = db1.

         Evaluation shape: the init result is let-bound ONCE (its effects run exactly
         once, before the elements — mirroring the reference, which runs init even when
         the scrutinee is not a list); a non-[Rval.List] scrutinee yields the init
         accumulator (the empty fold, adr-0012 §Decision 2). An Err.throw inside the
         body is a native exception, so it aborts the fold_left mid-list exactly like
         the reference's OErr short-circuit. The [_aN]/[_lN] locals use the same
         depth-suffix freshness scheme as Match's [_sN]. *)
      let name_elem = bind_name env in                (* = db1 (pushed first) *)
      let name_acc  = bind_name (name_elem :: env) in (* = db0 (pushed last) *)
      let env' = name_acc :: name_elem :: env in
      let depth = List.length env in
      Printf.sprintf
        "(let _a%d = %s in match %s with Rval.List _l%d -> List.fold_left (fun %s %s -> %s) _a%d _l%d | _ -> _a%d)"
        depth (emit_tm env init)
        (emit_val env lst) depth
        name_acc name_elem (emit_tm env' body)
        depth depth depth

let header =
  "(* Generated by rocq-eff-codegen (IR v2 R9). Source: theories/EffIR.v + Samples.v.\n\
  \   Direct-style; the EffIR monad has been erased. Do not edit manually.\n\
  \   See kb/spec/codegen.md and kb/architecture/decisions/adr-0013-journal-effect.md. *)\n\
   open Rkv\n"

(* R10 v1 (adr-0014-wf-checker §4): the pre-emission gate runs the EXTRACTED, PROVEN
   well-formedness checker [Wf.wf_tm] (theories/Wf.v — scope + arity + binder counts;
   soundness: no scope-Dstuck for wf programs) at depth 0 on every program. One
   implementation, two uses (proof subject + this gate); wf is NOT reimplemented in
   OCaml, and there is no opt-out. The loud failure goes to stderr; the raised
   [Codegen_error] makes the CLI driver exit nonzero, failing the whole run before ANY
   output is emitted. *)
let wf_gate (name : string) (t : tm) : unit =
  if not (Coqconv.bool_of_coq (Ref_extracted.Wf.wf_tm Ref_extracted.Datatypes.O t))
  then begin
    let msg = Printf.sprintf "program %s: ill-formed (wf_tm = false)" name in
    Printf.eprintf "%s\n%!" msg;
    raise (Codegen_error msg)
  end

(* Emit one direct-style [name () = …] per entry of a SINGLE-SOURCE program list (for
   rocqeteer itself: [Samples.all_programs], defined in Rocq and extracted, iterated by
   the thin CLI driver; consumers pass THEIR extracted list): adding a program is a
   one-line edit there, with no separate codegen/extraction list to keep in sync. Every
   program is wf-gated BEFORE the first byte of output. Plain [pp_print_string] with no
   boxes or break hints keeps the emitted bytes identical to the historical
   [print_string]/[printf] output (property P4/NF5). *)
let emit_programs (fmt : Format.formatter) programs : unit =
  let programs =
    Coqconv.list_of_coq programs
    |> List.map (fun pair ->
           match pair with
           | Ref_extracted.Datatypes.Coq_pair (cname, t) ->
               (Coqconv.string_of_coq cname, t))
  in
  List.iter (fun (name, t) -> wf_gate name t) programs;
  Format.pp_print_string fmt header;
  List.iter
    (fun (name, t) ->
       Format.pp_print_string fmt (Printf.sprintf "let %s () = %s\n" name (emit_tm [] t)))
    programs;
  Format.pp_print_flush fmt ()
