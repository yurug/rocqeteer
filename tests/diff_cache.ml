(** Cache-effect differential test (metamorphic). [sample_cache] memoizes 1 at cache key
    "0" and writes it to store key "1". The store observable must be identical across
    THREE runs:
      reference (empty cache, miss path), fast with an empty cache (miss), and fast with a
      correctly pre-filled cache (hit).
    Equal results witness that the cache is observationally invisible
    (kb/spec/effect-signatures.md; proven in theories/Cache.v). The cache itself is never
    observed.

    R4+R5 (adr-0011): cache and store keys are byte strings; store entries carry
    (value, deadline). *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let now = Z.zero
let key_bytes (k : Z.t) : bytes = Bytes.of_string (Z.to_string k)

let norm bindings =
  Coqconv.list_of_coq bindings
  |> List.map (fun p ->
         match p with
         | D.Coq_pair (k, e) ->
             (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
  |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)

let ref_kv (pairs : (Z.t * Z.t) list) : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let m0 =
    List.fold_left
      (fun m (k, v) ->
         E.M.add (Coqconv.coq_string_of_bytes (key_bytes k))
           (Coqconv.coq_entry_of_rval (Rkv.Rval.Int v, None)) m)
      E.M.empty pairs
  in
  match E.observe_full E.DUnit (Coqconv.coqz_of_z now) m0 S.sample_cache with
  | D.Coq_pair (D.Coq_pair (_o, bs), _tr) -> norm bs

(* [prefill] optionally seeds the cache with ("0" -> Rval.Int 1) to exercise the HIT path. *)
let fast_kv (prefill : bool) (pairs : (Z.t * Z.t) list)
    : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let kvtbl = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace kvtbl (key_bytes k) (Rkv.Rval.Int v, None)) pairs;
  let ctbl = Rkv.Cache.T.create 8 in
  if prefill then Rkv.Cache.T.replace ctbl (Bytes.of_string "0") (Rkv.Rval.Int (Z.of_int 1));
  Rkv.Cache.run ctbl (fun () ->
      Rkv.Runtime.with_store_and_time ~source:(fun () -> now) kvtbl
        (fun () -> ignore (Gen.sample_cache ())));
  Rkv.Kv.observe ~now kvtbl

let entry_eq (v1, d1) (v2, d2) = Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2

let eq a b =
  List.length a = List.length b
  && List.for_all2
       (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2)
       a b

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260621
let rng = Random.State.make [| seed |]
let gen_state () =
  List.init (Random.State.int rng 8)
    (fun _ ->
       (Z.of_int (2 + Random.State.int rng 10), Z.of_int (Random.State.int rng 1000)))

let () =
  let n = 3000 in
  let fails = ref 0 in
  for _ = 1 to n do
    let pairs = gen_state () in
    let r = ref_kv pairs and miss = fast_kv false pairs and hit = fast_kv true pairs in
    (* reference == fast(miss), and the metamorphic cache-hit == cache-miss invisibility *)
    if not (eq r miss && eq miss hit) then incr fails
  done;
  Printf.printf "states=%d fails=%d (each: reference == fast-miss == fast-hit)\n" n !fails;
  if !fails = 0 then
    print_endline "CACHE DIFFERENTIAL OK: cache is observationally invisible (hit == miss == reference)"
  else exit 1
