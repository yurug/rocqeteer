(** Cache-effect differential test (metamorphic). [sample_cache] memoizes 1 at key 0 and
    writes it to key 1. The KV observable must be identical across THREE runs:
      reference (empty cache, miss path), fast with an empty cache (miss), and fast with a
      correctly pre-filled cache (hit).
    Equal results witness that the cache is observationally invisible (kb/spec/effect-signatures.md;
    proven in theories/Cache.v). The cache itself is never observed. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let z_of = Coqconv.z_of_coqz

let norm bindings =
  Coqconv.list_of_coq bindings
  |> List.map (fun p ->
         match p with
         | D.Coq_pair (k, E.DInt v) -> (z_of k, z_of v)
         | D.Coq_pair (_, _) -> failwith "reference: non-int KV value")
  |> List.sort (fun (a, _) (b, _) -> Z.compare a b)

let ref_kv (pairs : (Z.t * Z.t) list) : (Z.t * Z.t) list =
  let m0 =
    List.fold_left
      (fun m (k, v) -> E.M.add (Coqconv.coqz_of_z k) (E.DInt (Coqconv.coqz_of_z v)) m)
      E.M.empty pairs
  in
  match E.observe_full E.DUnit m0 S.sample_cache with
  | D.Coq_pair (D.Coq_pair (_o, bs), _tr) -> norm bs

(* [prefill] optionally seeds the cache with (0 -> 1) to exercise the HIT path. *)
let fast_kv (prefill : bool) (pairs : (Z.t * Z.t) list) : (Z.t * Z.t) list =
  let kvtbl = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace kvtbl k v) pairs;
  let ctbl = Rkv.Cache.T.create 8 in
  if prefill then Rkv.Cache.T.replace ctbl (Z.of_int 0) (Z.of_int 1);
  Rkv.Cache.run ctbl (fun () -> Rkv.Kv.run kvtbl (fun () -> ignore (Gen.sample_cache ())));
  Rkv.Kv.observe kvtbl

let eq a b =
  List.length a = List.length b
  && List.for_all2 (fun (k1, v1) (k2, v2) -> Z.equal k1 k2 && Z.equal v1 v2) a b

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260621
let rng = Random.State.make [| seed |]
let gen_state () = List.init (Random.State.int rng 8) (fun _ -> (Z.of_int (2 + Random.State.int rng 10), Z.of_int (Random.State.int rng 1000)))

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
