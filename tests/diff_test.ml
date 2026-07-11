(** Step-1 differential test: the SAME extracted [prog0] drives the reference interpreter
    and the generated fast OCaml, and their observables must match.

    This is the bridge spike's acceptance check (kb/plan.md Step 1): it proves one EffIR
    value flows through Rocq -> extraction -> (a) reference interpreter and (b) codegen ->
    OCaml -> effect handler, with identical observable results.

    R4+R5 (adr-0011): keys are byte strings; entries carry (value, optional deadline);
    both sides run at one instant (now = 0 — prog0 is time-independent) and the fast side
    is wrapped by the single Time+Store composition point. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes

let now = Z.zero

(* Reference observable: run the extracted interpreter and normalize the LIVE bindings.
   Keys bridge via bytes_of_coq_string; entries via rval_entry_of_coq. *)
let ref_observe () : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let bindings =
    match E.observe_full E.DUnit (Coqconv.coqz_of_z now) E.M.empty E.prog0 with
    | D.Coq_pair (D.Coq_pair (_o, bs), _tr) -> bs
  in
  Coqconv.list_of_coq bindings
  |> List.map (fun kv ->
         match kv with
         | D.Coq_pair (k, e) ->
             (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))

(* Fast observable: run the generated direct-style prog0 under Time ∘ Store (one source). *)
let fast_observe () : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let table = Rkv.Kv.T.create 16 in
  (match Rkv.Runtime.with_store_and_time_checked ~source:(fun () -> now) table
           (fun () -> ignore (Generated.Prog0_generated.prog0 ())) with
   | Ok () -> ()
   | Error e -> failwith ("fast prog0: " ^ Rkv.Kv.string_of_error e));
  Rkv.Kv.observe ~now table

let show_entry (v, dl) =
  Rkv.Rval.to_string v ^ (match dl with None -> "" | Some d -> "@" ^ Z.to_string d)

let show l =
  "[" ^ String.concat "; "
    (List.map (fun (k, e) -> Printf.sprintf "%s->%s" (Bytes.to_string k) (show_entry e)) l)
  ^ "]"

let entry_eq (v1, d1) (v2, d2) = Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2

let () =
  let r = ref_observe () and f = fast_observe () in
  Printf.printf "reference: %s\nfast:      %s\n" (show r) (show f);
  let eq =
    List.length r = List.length f
    && List.for_all2
         (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2)
         r f
  in
  if eq then print_endline "STEP1 BRIDGE OK: reference == fast on prog0"
  else (
    print_endline "STEP1 BRIDGE MISMATCH";
    exit 1)
