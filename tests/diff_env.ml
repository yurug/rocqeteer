(** Env-effect differential test: the read-only context flows identically through the
    reference interpreter (the [ctx] field of [world]) and the fast side (the [Env.run]
    handler wrapped around the Time+Store stack). For [sample_env] (ask; put "1" := asked
    value), key "1" must end up holding the context on both sides, over random ctx +
    initial state.

    R4+R5 (adr-0011): keys are decimal byte strings; entries carry (value, deadline). *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let now = Z.zero
let key_bytes (k : Z.t) : bytes = Bytes.of_string (Z.to_string k)
let key1 = key_bytes Z.one

let ref_state (ctx : Z.t) (pairs : (Z.t * Z.t) list)
    : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let m0 =
    List.fold_left
      (fun m (k, v) ->
         E.M.add (Coqconv.coq_string_of_bytes (key_bytes k))
           (Coqconv.coq_entry_of_rval (Rkv.Rval.Int v, None)) m)
      E.M.empty pairs
  in
  let bindings =
    match E.observe_full (E.DInt (Coqconv.coqz_of_z ctx)) (Coqconv.coqz_of_z now) m0
            S.sample_env with
    | D.Coq_pair (D.Coq_pair (D.Coq_pair (_o, bs), _tr), _jr) -> bs
  in
  Coqconv.list_of_coq bindings
  |> List.map (fun p ->
         match p with
         | D.Coq_pair (k, e) ->
             (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
  |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)

let fast_state (ctx : Z.t) (pairs : (Z.t * Z.t) list)
    : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace table (key_bytes k) (Rkv.Rval.Int v, None)) pairs;
  (* Env handler outermost (Ask propagates out of the Time+Store stack to it). *)
  Rkv.Env.run (Rkv.Rval.Int ctx) (fun () ->
      Rkv.Runtime.with_store_and_time ~source:(fun () -> now) table
        (fun () -> ignore (Gen.sample_env ())));
  Rkv.Kv.observe ~now table

let entry_eq (v1, d1) (v2, d2) = Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2

let state_eq a b =
  List.length a = List.length b
  && List.for_all2
       (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2)
       a b

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260621
let rng = Random.State.make [| seed |]
let gen_z () = Z.of_int (Random.State.int rng 2000 - 1000)
let gen_state () =
  List.init (Random.State.int rng 8)
    (fun _ -> (Z.of_int (Random.State.int rng 12 - 2), gen_z ()))

let show_entry (v, dl) =
  Rkv.Rval.to_string v ^ (match dl with None -> "" | Some d -> "@" ^ Z.to_string d)

let show l =
  "[" ^ String.concat "; "
    (List.map (fun (k, e) -> Printf.sprintf "%s=%s" (Bytes.to_string k) (show_entry e)) l)
  ^ "]"

let () =
  let n = 3000 in
  let fails = ref 0 and ctx_landed = ref 0 in
  for _ = 1 to n do
    let ctx = gen_z () and pairs = gen_state () in
    let r = ref_state ctx pairs and f = fast_state ctx pairs in
    (* sanity: key "1" holds (Int ctx, no deadline) on the reference side *)
    if List.exists
         (fun (k, (v, dl)) ->
            Bytes.equal k key1 && Rkv.Rval.equal v (Rkv.Rval.Int ctx) && dl = None)
         r
    then incr ctx_landed;
    if not (state_eq r f) then (
      incr fails;
      Printf.printf "MISMATCH (RSEED=%d) ctx=%s\n  ref =%s\n  fast=%s\n"
        seed (Z.to_string ctx) (show r) (show f))
  done;
  Printf.printf "states=%d fails=%d | ctx-landed-at-key1=%d/%d\n" n !fails !ctx_landed n;
  if !fails = 0 && !ctx_landed = n then
    print_endline "ENV DIFFERENTIAL OK: read-only context flows identically; ask value lands at key 1"
  else (
    if !ctx_landed <> n then print_endline "ENV: context did not always reach key 1";
    exit 1)
