(** rocq-eff-codegen (slice 1): lower an extracted EffIR [tm] to direct-style OCaml 5.

    The monad is ERASED by construction: [Bind] -> [let], [Perform] -> a [Kv.*] call,
    [MatchOpt] -> [match]. No [Bind]/free-monad constructor survives into the output
    (property P3). Out-of-fragment input fails loudly rather than emitting unsound code
    (kb/spec/codegen.md, kb/spec/error-taxonomy.md).

    Slice-1 scope: it lowers exactly the four [tm] forms and the [val] forms that
    [prog0] needs; anything else raises [Codegen_error].

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

let rec emit_tm (env : string list) (t : tm) : string =
  match t with
  | Ret v -> emit_val env v
  | Bind (t1, t2) ->
      let name = bind_name env in
      Printf.sprintf "(let %s = %s in %s)" name (emit_tm env t1)
        (emit_tm (name :: env) t2)
  | Perform (o, args) -> emit_perform env o (Coqconv.list_of_coq args)
  | MatchOpt (scrut, none, some) ->
      let name = bind_name env in
      Printf.sprintf "(match %s with Rval.None -> %s | Rval.Some %s -> %s | _ -> raise Rval.Stuck)"
        (emit_val env scrut) (emit_tm env none) name
        (emit_tm (name :: env) some)
  | Repeat (n, body) ->
      (* bounded loop -> a native for-loop; the body runs n times for its effects *)
      Printf.sprintf "(for _i = 1 to %d do ignore (%s) done)" (Coqconv.int_of_nat n)
        (emit_tm env body)

let header =
  "(* Generated by rocq-eff-codegen (slice 1). Source: theories/EffIR.v + Samples.v.\n\
  \   Direct-style; the EffIR monad has been erased. Do not edit manually.\n\
  \   See kb/spec/codegen.md. *)\n\
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
