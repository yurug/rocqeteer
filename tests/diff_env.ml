(** Env-effect differential test: the read-only context flows identically through the
    reference interpreter (the [ctx] parameter of [run]) and the fast side (the [Env.run]
    handler wrapped around the KV handler). For [sample_env] (ask; put 1 := asked value),
    key 1 must end up holding the context on both sides, over random ctx + initial state. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let ref_state (ctx : Z.t) (pairs : (Z.t * Z.t) list) : (Z.t * Rkv.Rval.t) list =
  let m0 =
    List.fold_left
      (fun m (k, v) ->
         E.M.add (Coqconv.coqz_of_z k) (E.DInt (Coqconv.coqz_of_z v)) m)
      E.M.empty pairs
  in
  let bindings =
    match E.observe_full (E.DInt (Coqconv.coqz_of_z ctx)) m0 S.sample_env with
    | D.Coq_pair (D.Coq_pair (_o, bs), _tr) -> bs
  in
  Coqconv.list_of_coq bindings
  |> List.map (fun p ->
         match p with
         | D.Coq_pair (k, v) -> (Coqconv.z_of_coqz k, Coqconv.rval_of_dval v))
  |> List.sort (fun (a, _) (b, _) -> Z.compare a b)

let fast_state (ctx : Z.t) (pairs : (Z.t * Z.t) list) : (Z.t * Rkv.Rval.t) list =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace table k (Rkv.Rval.Int v)) pairs;
  (* Env handler outermost (Ask propagates out of the KV handler to it), KV handler inner.
     Context is now Rval.t: wrap the Z.t ctx as Rval.Int. *)
  Rkv.Env.run (Rkv.Rval.Int ctx) (fun () ->
      Rkv.Kv.run table (fun () -> ignore (Gen.sample_env ())));
  Rkv.Kv.observe table

let state_eq a b =
  List.length a = List.length b
  && List.for_all2
       (fun (k1, v1) (k2, v2) -> Z.equal k1 k2 && Rkv.Rval.equal v1 v2)
       a b

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260621
let rng = Random.State.make [| seed |]
let gen_z () = Z.of_int (Random.State.int rng 2000 - 1000)
let gen_state () =
  List.init (Random.State.int rng 8)
    (fun _ -> (Z.of_int (Random.State.int rng 12 - 2), gen_z ()))

let show l =
  "[" ^ String.concat "; "
    (List.map (fun (k, v) -> Printf.sprintf "%s=%s" (Z.to_string k) (Rkv.Rval.to_string v)) l)
  ^ "]"

let () =
  let n = 3000 in
  let fails = ref 0 and ctx_landed = ref 0 in
  for _ = 1 to n do
    let ctx = gen_z () and pairs = gen_state () in
    let r = ref_state ctx pairs and f = fast_state ctx pairs in
    (* sanity: key 1 holds Rval.Int ctx on the reference side (the asked value flowed in) *)
    if List.exists
         (fun (k, v) -> Z.equal k Z.one && Rkv.Rval.equal v (Rkv.Rval.Int ctx))
         r
    then incr ctx_landed;
    if not (state_eq r f) then (
      incr fails;
      Printf.printf "MISMATCH (RSEED=%d) ctx=%s state=%s\n  ref =%s\n  fast=%s\n"
        seed (Z.to_string ctx)
        (show (List.map (fun (k,v) -> (k, Rkv.Rval.Int v)) pairs))
        (show r) (show f))
  done;
  Printf.printf "states=%d fails=%d | ctx-landed-at-key1=%d/%d\n" n !fails !ctx_landed n;
  if !fails = 0 && !ctx_landed = n then
    print_endline "ENV DIFFERENTIAL OK: read-only context flows identically; ask value lands at key 1"
  else (
    if !ctx_landed <> n then print_endline "ENV: context did not always reach key 1";
    exit 1)
