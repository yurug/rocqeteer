(** Mode-K differential test for the CACHE consolidation (ADR-0016 C2,
    theories/ElabNs.v — the FAITHFUL store-backed cache, §Corrections 1).

    [sample_cache] (get-or-compute-and-put memoization over cache key "0", store
    key "1") runs ELABORATED (generated/progk_generated.ml = the full tower) against
    KERNEL realizers only: no cache realizer exists in the stack — cache entries
    live in the "c" region of the kernel store.

    Protocol per round (adversarially seeded user stores, boundary instants):
      COLD: fresh table, seeded "u" region only    -> obs == reference
            and the "c" region is NONEMPTY afterwards (the cache write really
            landed in the consolidated store — coverage CW)
      WARM: run again on the SAME table            -> outcome == reference outcome
            and user state == reference state (the HIT path — the "c" region is
            populated, so OCacheGet returns Some through the store; this is the
            metamorphic fast-hit == fast-miss == reference of diff_cache, now over
            the consolidation — coverage CH).

    The put-then-get shape inside [sample_cache] is exactly what refutes the null
    cache elaboration (theories/ElabNs.v [mutant_cache_rejected]).

    Seeded and reproducible: RSEED=<n> replays. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module GenK = Generated.Progk_generated

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260720
let rng = Random.State.make [| seed |]

type entry = Rkv.Rval.t * Z.t option
type obs = { out : Rkv.Rval.t option; state : (bytes * entry) list }

let entry_eq ((v1, d1) : entry) ((v2, d2) : entry) =
  Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2

let state_eq a b =
  List.length a = List.length b
  && List.for_all2 (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2) a b

let obs_eq a b = Option.equal Rkv.Rval.equal a.out b.out && state_eq a.state b.state

let show_entry (v, dl) =
  Rkv.Rval.to_string v ^ (match dl with None -> "" | Some d -> "@" ^ Z.to_string d)

let show_obs o =
  Printf.sprintf "(%s, [%s])"
    (match o.out with None -> "throw" | Some v -> Rkv.Rval.to_string v)
    (String.concat "; "
       (List.map (fun (k, e) ->
            Printf.sprintf "%s=%s" (Rkv.Rval.to_string (Rkv.Rval.Bytes k)) (show_entry e))
          o.state))

let ref_obs (term : E.tm) (now : Z.t) (pairs : (bytes * entry) list) : obs =
  let m0 =
    List.fold_left
      (fun m (k, e) ->
         E.M.add (Coqconv.coq_string_of_bytes k) (Coqconv.coq_entry_of_rval e) m)
      E.M.empty pairs
  in
  let oc, bindings =
    match E.observe_full E.DUnit (Coqconv.coqz_of_z now) m0 term with
    | D.Coq_pair (D.Coq_pair (D.Coq_pair (o, bs), _tr), _jr) -> (o, bs)
  in
  let out =
    match oc with E.ORet v -> Some (Coqconv.rval_of_dval v) | E.OErr _ -> None
  in
  let state =
    Coqconv.list_of_coq bindings
    |> List.map (fun p ->
           match p with
           | D.Coq_pair (k, e) ->
               (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
    |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)
  in
  { out; state }

(* --- fast-K plumbing (the diff_store_k conventions) ---------------------------- *)

let pack_entry ((v, dl) : entry) : Rkv.Rval.t =
  Rkv.Rval.Pair
    (v, match dl with
        | None -> Rkv.Rval.None
        | Some d -> Rkv.Rval.Some (Rkv.Rval.Int d))

let esc_u (k : bytes) : bytes = Bytes.cat (Bytes.of_string "u") k

let unpack_live (now : Z.t) ((km, pv) : bytes * Rkv.Rval.t) : (bytes * entry) option =
  if Bytes.length km = 0 then failwith "diff_cache_k: empty kernel key"
  else
    match Bytes.get km 0 with
    | 'u' ->
        let k = Bytes.sub km 1 (Bytes.length km - 1) in
        (match pv with
         | Rkv.Rval.Pair (v, Rkv.Rval.None) -> Some (k, (v, None))
         | Rkv.Rval.Pair (v, Rkv.Rval.Some (Rkv.Rval.Int d)) ->
             if Z.leq now d then Some (k, (v, Some d)) else None
         | _ -> failwith "diff_cache_k: non-packed kernel value")
    | 'c' | 'j' -> None
    | _ -> failwith "diff_cache_k: kernel key outside the u/c/j regions"

let seed_table (pairs : (bytes * entry) list) =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, e) -> Rkv.Kv.T.replace table (esc_u k) (pack_entry e)) pairs;
  table

let run_k table (fn : unit -> Rkv.Rval.t) (now : Z.t) : obs =
  let out =
    match Rkv.Time.run (fun () -> now) (fun () -> Rkv.Kv.run_kernel_checked table fn) with
    | Ok v -> Some v
    | Error e -> failwith ("diff_cache_k fast: " ^ Rkv.Kv.string_of_error e)
  in
  { out; state = List.filter_map (unpack_live now) (Rkv.Kv.observe_kernel table) }

let cache_region_nonempty table =
  Rkv.Kv.observe_kernel table
  |> List.exists (fun (km, _) -> Bytes.length km > 0 && Bytes.get km 0 = 'c')

(* --- generators (store seeds around sample_cache's keys) ----------------------- *)

let key_pool : bytes list =
  [ Bytes.empty; Bytes.of_string "\x00"; Bytes.of_string "0"; Bytes.of_string "1";
    Bytes.of_string "a"; Bytes.of_string "a\x00"; Bytes.make 200 'C' ]

let gen_key () = List.nth key_pool (Random.State.int rng (List.length key_pool))

let gen_value () : Rkv.Rval.t =
  match Random.State.int rng 3 with
  | 0 -> Rkv.Rval.Int (Z.of_int (Random.State.int rng 2000 - 1000))
  | 1 -> Rkv.Rval.Bytes (Bytes.of_string "v\x00\xff")
  | _ -> Rkv.Rval.Bool (Random.State.bool rng)

let gen_deadline (now : Z.t) : Z.t option =
  match Random.State.int rng 5 with
  | 0 -> None
  | 1 -> Some (Z.sub now Z.one)
  | 2 -> Some now
  | 3 -> Some (Z.add now Z.one)
  | _ -> Some (Z.of_int (Random.State.int rng 2000))

let gen_now () : Z.t =
  match Random.State.int rng 4 with
  | 0 -> Z.zero
  | 1 -> Z.of_int (-5)
  | 2 -> Z.of_string "4611686018427387904"
  | _ -> Z.of_int (Random.State.int rng 3000)

let gen_state (now : Z.t) : (bytes * entry) list =
  let n = Random.State.int rng 5 in
  List.init n (fun _ -> (gen_key (), (gen_value (), gen_deadline now)))
  |> List.fold_left (fun acc (k, e) ->
         (k, e) :: List.filter (fun (k', _) -> not (Bytes.equal k k')) acc) []

(* --- main ----------------------------------------------------------------------- *)

let () =
  let n = 3000 in
  let fails = ref 0 in
  let cov_cw = ref false and cov_ch = ref false in
  for _ = 1 to n do
    let now = gen_now () in
    let pairs = gen_state now in
    let r = ref_obs S.sample_cache now pairs in
    let table = seed_table pairs in
    let cold = run_k table GenK.sample_cache now in
    if not (obs_eq r cold) then (
      incr fails;
      Printf.printf "K-CACHE COLD MISMATCH (RSEED=%d) now=%s\n  ref =%s\n  cold=%s\n"
        seed (Z.to_string now) (show_obs r) (show_obs cold));
    if cache_region_nonempty table then cov_cw := true;
    (* WARM: the "c" region is populated -> the HIT path runs through the store *)
    let warm = run_k table GenK.sample_cache now in
    if not (obs_eq r warm) then (
      incr fails;
      Printf.printf "K-CACHE WARM MISMATCH (RSEED=%d) now=%s\n  ref =%s\n  warm=%s\n"
        seed (Z.to_string now) (show_obs r) (show_obs warm))
    else if cache_region_nonempty table then cov_ch := true
  done;
  Printf.printf
    "MODE-K CACHE rounds=%d fails=%d | coverage: CW(cache-write-in-store)=%b CH(hit-path==ref)=%b\n"
    n !fails !cov_cw !cov_ch;
  if !fails = 0 && !cov_cw && !cov_ch then
    print_endline
      "MODE-K CACHE OK: faithful consolidation — cold == warm == reference, no cache realizer in the stack"
  else exit 1
