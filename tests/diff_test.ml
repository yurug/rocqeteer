(** Step-1 differential test: the SAME extracted [prog0] drives the reference interpreter
    and the generated fast OCaml, and their observables must match.

    This is the bridge spike's acceptance check (kb/plan.md Step 1): it proves one EffIR
    value flows through Rocq -> extraction -> (a) reference interpreter and (b) codegen ->
    OCaml -> effect handler, with identical observable results. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes

(* Reference KV values are always [DInt] in slice 1; anything else is a real divergence. *)
let dval_to_z (d : E.dval) : Z.t =
  match d with
  | E.DInt z -> Coqconv.z_of_coqz z
  | _ -> failwith "reference produced a non-int KV value (unexpected in slice 1)"

(* Reference observable: run the extracted interpreter and normalize the FMapAVL state. *)
let ref_observe () : (Z.t * Z.t) list =
  let pair = E.observe E.DUnit E.prog0 in
  let bindings = match pair with D.Coq_pair (_result, bs) -> bs in
  Coqconv.list_of_coq bindings
  |> List.map (fun kv ->
         match kv with D.Coq_pair (k, v) -> (Coqconv.z_of_coqz k, dval_to_z v))

(* Fast observable: run the generated direct-style prog0 under the KV deep handler. *)
let fast_observe () : (Z.t * Z.t) list =
  let table = Rkv.Kv.T.create 16 in
  (match Rkv.Kv.run_checked table Generated.Prog0_generated.prog0 with
   | Ok () -> ()
   | Error e -> failwith ("fast prog0: " ^ Rkv.Kv.string_of_error e));
  Rkv.Kv.observe table

let show l =
  "[" ^ String.concat "; " (List.map (fun (k, v) -> Printf.sprintf "%s->%s" (Z.to_string k) (Z.to_string v)) l) ^ "]"

let () =
  let r = ref_observe () and f = fast_observe () in
  Printf.printf "reference: %s\nfast:      %s\n" (show r) (show f);
  let eq =
    List.length r = List.length f
    && List.for_all2 (fun (k1, v1) (k2, v2) -> Z.equal k1 k2 && Z.equal v1 v2) r f
  in
  if eq then print_endline "STEP1 BRIDGE OK: reference == fast on prog0"
  else (
    print_endline "STEP1 BRIDGE MISMATCH";
    exit 1)
