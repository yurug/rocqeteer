(** rocq-eff-codegen (IR v2 R7: structured values): lower an extracted EffIR [tm] to
    direct-style OCaml 5. R7 (adr-0010-structured-values) adds [VTag]/[VList] to
    [emit_val] (-> [Rval.Tag]/[Rval.List]) and [PTag] to [emit_branch] (a literal-tag
    match with a payload binder, chained like [PSome]).

    The monad is ERASED by construction: [Bind] -> [let], [Perform] -> a [Kv.*] call,
    [Match] -> chained match/if (adr-0008-general-match §Decision 4). No [Bind]/free-monad
    constructor survives into the output (property P3). Out-of-fragment input fails loudly
    rather than emitting unsound code (kb/spec/codegen.md, kb/spec/error-taxonomy.md).

    Values are typed as [Rval.t] at effect boundaries (IR v2 milestone 1).  Keys at
    KV/Cache call sites stay [Z.t] — bytes keys are a later milestone.  When generated
    code consumes a KV/cache value as an integer (e.g. [VSucc] applied to a bound
    variable), it emits a match on [Rval.Int]; the fallback raises [Rval.Stuck], mirroring
    the reference interpreter's [Dstuck] sentinel on ill-typed values. *)

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

(* [emit_key] emits a [Z.t] expression for a KV/Cache key argument.
   Only [VInt] and [VZero] are key-literal forms; [VVar] is NOT used as a key in slice 1. *)
let emit_key (env : string list) (v : coq_val) : string =
  match v with
  | VInt z  -> emit_z z
  | VZero   -> "Z.zero"
  | VVar n  -> (
      match List.nth_opt env (Coqconv.int_of_nat n) with
      | Some name -> name   (* a VVar used as a key — caller must ensure it is Z.t-shaped *)
      | None -> raise (Codegen_error "VVar index out of scope (key)"))
  | _ -> raise (Codegen_error "non-integer value used in key position")

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

(* KV operations lower to the curried public wrappers (kb/spec/effect-signatures.md,
   Resolution 7). Wrong arity is a codegen error, not a silent cast.
   Key arguments use [emit_key] (Z.t); value arguments use [emit_val] (Rval.t). *)
let emit_perform (env : string list) (o : op) (args : coq_val list) : string =
  match o, args with
  | OGet,    [k]     -> Printf.sprintf "(Kv.get %s)" (emit_key env k)
  | OPut,    [k; v]  -> Printf.sprintf "(Kv.put %s %s)" (emit_key env k) (emit_val env v)
  | ODelete, [k]     -> Printf.sprintf "(Kv.delete %s)" (emit_key env k)
  | OThrow,  [e]     -> Printf.sprintf "(Err.throw %s)" (emit_val env e)
  | OAsk,    []      -> "(Env.ask ())"
  | OTrace,  [v]     -> Printf.sprintf "(Trace.emit %s)" (emit_val env v)
  | OCacheGet, [k]   -> Printf.sprintf "(Cache.get %s)" (emit_key env k)
  | OCachePut, [k;v] -> Printf.sprintf "(Cache.put %s %s)" (emit_key env k) (emit_val env v)
  | _ -> raise (Codegen_error "effect operation applied at the wrong arity")

(* Helper: emit escaped bytes literal string from an ascii list (same escaping as emit_val). *)
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

let header =
  "(* Generated by rocq-eff-codegen (IR v2 R7). Source: theories/EffIR.v + Samples.v.\n\
  \   Direct-style; the EffIR monad has been erased. Do not edit manually.\n\
  \   See kb/spec/codegen.md and kb/architecture/decisions/adr-0010-structured-values.md. *)\n\
   open Rkv\n"

(* Emit one direct-style [name () = …] per entry of the SINGLE-SOURCE program list
   [Samples.all_programs] (defined in Rocq, extracted here): adding a program is a one-line
   edit there, with no separate codegen/extraction list to keep in sync. *)
let () =
  print_string header;
  Coqconv.list_of_coq Ref_extracted.Samples.all_programs
  |> List.iter (fun pair ->
         match pair with
         | Ref_extracted.Datatypes.Coq_pair (cname, t) ->
             Printf.printf "let %s () = %s\n" (Coqconv.string_of_coq cname) (emit_tm [] t))
