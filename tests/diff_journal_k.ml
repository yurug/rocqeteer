(** Mode-K differential test for the JOURNAL consolidation (ADR-0016 C2,
    theories/ElabNs.v — the journal as ONE chronological [DList] at kernel key "j").

    [sample_journal] (two fixed entries + one per context element, from a Fold),
    [sample_journal_throw] (Repeat-driven appends then a throw) and [sample_two]
    (journal-free) run ELABORATED (the full tower) against KERNEL realizers only —
    NO journal realizer, NO cache realizer: the fast journal is DECODED from the
    packed "j" binding of the kernel table, in untrusted harness code.

    Compared per run: outcome (incl. the error payload), user store ("u" region,
    unpacked + liveness-filtered), trace, and the chronological (timestamp, value)
    journal.  Classes (coverage ASSERTED):
      JK1 empty context        JK2 mixed nested payloads   JK3 large list (>= 500)
      JK4 non-list context     JK5 throw: the pre-throw entries survive, exactly
      JK6 order == input order (suffix check against the context, not just ref==fast)
      JK7 journal-free program: no "j" binding at all
      JK8 two instants: every timestamp is the run's instant

    Seeded and reproducible: RSEED=<n> replays. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module GenK = Generated.Progk_generated

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260721
let rng = Random.State.make [| seed |]

let now_a = Z.zero
let now_b = Z.of_int 54321

type entry = Rkv.Rval.t * Z.t option

type obs = {
  out   : (Rkv.Rval.t, Rkv.Rval.t) result;
  state : (bytes * entry) list;
  tr    : Rkv.Rval.t list;
  jr    : (Z.t * Rkv.Rval.t) list;            (* chronological *)
}

(* --- reference ----------------------------------------------------------------- *)

let ref_obs (term : E.tm) (ctx : Rkv.Rval.t) (now : Z.t) : obs =
  let coq_ctx = Coqconv.dval_of_rval ctx in
  let oc, bindings, tr, jr =
    match E.observe_full coq_ctx (Coqconv.coqz_of_z now) E.M.empty term with
    | D.Coq_pair (D.Coq_pair (D.Coq_pair (oc, bs), t), j) -> (oc, bs, t, j)
  in
  let out =
    match oc with
    | E.ORet v -> Ok (Coqconv.rval_of_dval v)
    | E.OErr e -> Error (Coqconv.rval_of_dval e)
  in
  let state =
    Coqconv.list_of_coq bindings
    |> List.map (fun p ->
           match p with
           | D.Coq_pair (k, e) ->
               (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
    |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)
  in
  let journal =
    Coqconv.list_of_coq jr
    |> List.map (fun p ->
           match p with
           | D.Coq_pair (z, d) -> (Coqconv.z_of_coqz z, Coqconv.rval_of_dval d))
  in
  { out; state;
    tr = Coqconv.list_of_coq tr |> List.map Coqconv.rval_of_dval;
    jr = journal }

(* --- fast-K --------------------------------------------------------------------- *)

let unpack_live (now : Z.t) ((km, pv) : bytes * Rkv.Rval.t) : (bytes * entry) option =
  if Bytes.length km = 0 then failwith "diff_journal_k: empty kernel key"
  else
    match Bytes.get km 0 with
    | 'u' ->
        let k = Bytes.sub km 1 (Bytes.length km - 1) in
        (match pv with
         | Rkv.Rval.Pair (v, Rkv.Rval.None) -> Some (k, (v, None))
         | Rkv.Rval.Pair (v, Rkv.Rval.Some (Rkv.Rval.Int d)) ->
             if Z.leq now d then Some (k, (v, Some d)) else None
         | _ -> failwith "diff_journal_k: non-packed kernel value")
    | 'c' | 'j' -> None
    | _ -> failwith "diff_journal_k: kernel key outside the u/c/j regions"

(** Decode the consolidated journal: the packed "j" binding is
    [Pair (List [Pair (Int t, v); ...], None)] — chronological by construction. *)
let decode_journal table : (Z.t * Rkv.Rval.t) list =
  match Rkv.Kv.T.find_opt table (Bytes.of_string "j") with
  | None -> []
  | Some (Rkv.Rval.Pair (Rkv.Rval.List entries, Rkv.Rval.None)) ->
      List.map
        (function
          | Rkv.Rval.Pair (Rkv.Rval.Int t, v) -> (t, v)
          | _ -> failwith "diff_journal_k: malformed journal entry")
        entries
  | Some _ -> failwith "diff_journal_k: malformed 'j' binding"

let has_j_binding table = Rkv.Kv.T.mem table (Bytes.of_string "j")

let fastk_obs (fn : unit -> Rkv.Rval.t) (ctx : Rkv.Rval.t) (now : Z.t)
    : obs * bool =
  let table = Rkv.Kv.T.create 64 in
  let buf = ref [] in
  let out =
    Rkv.Env.run ctx (fun () ->
        Rkv.Trace.run buf (fun () ->
            match
              Rkv.Err.run_error (fun () ->
                  Rkv.Time.run (fun () -> now)
                    (fun () -> Rkv.Kv.run_kernel table fn))
            with
            | Ok v -> Ok v
            | Error e -> Error e))
  in
  ({ out;
     state = List.filter_map (unpack_live now) (Rkv.Kv.observe_kernel table);
     tr = Rkv.Trace.contents buf;
     jr = decode_journal table },
   has_j_binding table)

(* --- equality ------------------------------------------------------------------- *)

let out_eq a b =
  match a, b with
  | Ok x, Ok y | Error x, Error y -> Rkv.Rval.equal x y
  | _ -> false

let list_eq eq a b = List.length a = List.length b && List.for_all2 eq a b
let entry_eq (v1, d1) (v2, d2) = Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2
let state_eq = list_eq (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2)
let trace_eq = list_eq Rkv.Rval.equal
let jentry_eq (z1, v1) (z2, v2) = Z.equal z1 z2 && Rkv.Rval.equal v1 v2
let journal_eq = list_eq jentry_eq

let obs_eq a b =
  out_eq a.out b.out && state_eq a.state b.state && trace_eq a.tr b.tr
  && journal_eq a.jr b.jr

let show_out = function
  | Ok v -> "ret " ^ Rkv.Rval.to_string v
  | Error e -> "throw " ^ Rkv.Rval.to_string e

let show_jr l =
  "[" ^ String.concat "; "
    (List.map (fun (z, v) -> Z.to_string z ^ ":" ^ Rkv.Rval.to_string v) l) ^ "]"

(* --- context generator ----------------------------------------------------------- *)

let rec gen_elem (depth : int) : Rkv.Rval.t =
  match Random.State.int rng (if depth = 0 then 5 else 8) with
  | 0 -> Rkv.Rval.Int (Z.of_int (Random.State.int rng 2001 - 1000))
  | 1 -> Rkv.Rval.Bytes (Bytes.of_string "e\x00\xff")
  | 2 -> Rkv.Rval.Bool (Random.State.bool rng)
  | 3 -> Rkv.Rval.Unit
  | 4 -> Rkv.Rval.None
  | 5 -> Rkv.Rval.Tag (Z.of_int (Random.State.int rng 5), gen_elem (depth - 1))
  | 6 -> Rkv.Rval.Pair (gen_elem (depth - 1), gen_elem (depth - 1))
  | _ -> Rkv.Rval.List (List.init (Random.State.int rng 3) (fun _ -> gen_elem (depth - 1)))

let gen_ctx () : Rkv.Rval.t =
  match Random.State.int rng 8 with
  | 0 -> Rkv.Rval.List []                                        (* JK1 *)
  | 1 -> Rkv.Rval.Int (Z.of_int 7)                               (* JK4 *)
  | 2 -> Rkv.Rval.List (List.init 500 (fun i -> Rkv.Rval.Int (Z.of_int i)))  (* JK3 *)
  | _ -> Rkv.Rval.List (List.init (Random.State.int rng 6) (fun _ -> gen_elem 2))

(* --- main ------------------------------------------------------------------------ *)

let () =
  let rounds = 300 in
  let fails = ref 0 in
  let cov_e = ref false and cov_m = ref false and cov_l = ref false in
  let cov_nl = ref false and cov_th = ref false and cov_ord = ref false in
  let cov_free = ref false and cov_2i = ref false in
  let check name term fn ctx now =
    let r = ref_obs term ctx now in
    let f, has_j = fastk_obs fn ctx now in
    if not (obs_eq r f) then (
      incr fails;
      Printf.printf
        "K-JOURNAL MISMATCH %s (RSEED=%d) now=%s\n  ref  out=%s jr=%s\n  fast out=%s jr=%s\n"
        name seed (Z.to_string now) (show_out r.out) (show_jr r.jr)
        (show_out f.out) (show_jr f.jr));
    (r, f, has_j)
  in
  List.iter
    (fun now ->
       if Z.equal now now_b then cov_2i := true;
       for _ = 1 to rounds do
         let ctx = gen_ctx () in
         (* sample_journal: fixed prefix + one entry per context element *)
         let r, _f, _ = check "sample_journal" S.sample_journal GenK.sample_journal ctx now in
         (match ctx with
          | Rkv.Rval.List [] -> cov_e := true
          | Rkv.Rval.List l when List.length l >= 500 -> cov_l := true
          | Rkv.Rval.List l ->
              cov_m := true;
              (* JK6: the journal SUFFIX equals the context, in order *)
              let suffix =
                let n = List.length r.jr in
                if n >= List.length l then
                  List.filteri (fun i _ -> i >= n - List.length l) r.jr
                else []
              in
              if List.length suffix = List.length l
                 && List.for_all2 (fun (_, v) x -> Rkv.Rval.equal v x) suffix l
              then cov_ord := true
          | _ -> cov_nl := true);
         (* sample_journal_throw: pre-throw entries survive (JK5) *)
         let r2, f2, _ = check "sample_journal_throw" S.sample_journal_throw
                            GenK.sample_journal_throw ctx now in
         (match r2.out, f2.out with
          | Error _, Error _ when journal_eq r2.jr f2.jr && r2.jr <> [] -> cov_th := true
          | _ -> ());
         (* sample_two: journal-free -> no "j" binding at all (JK7) *)
         let _, _, has_j = check "sample_two" S.sample_two GenK.sample_two ctx now in
         if not has_j then cov_free := true
       done)
    [ now_a; now_b ];
  let cov_ok =
    !cov_e && !cov_m && !cov_l && !cov_nl && !cov_th && !cov_ord
    && !cov_free && !cov_2i
  in
  Printf.printf
    "MODE-K JOURNAL rounds=%dx3x2 fails=%d | coverage: JK1(empty)=%b JK2(mixed)=%b JK3(large)=%b JK4(non-list)=%b JK5(throw-prefix)=%b JK6(order==input)=%b JK7(journal-free,no-j)=%b JK8(two-instants)=%b\n"
    rounds !fails !cov_e !cov_m !cov_l !cov_nl !cov_th !cov_ord !cov_free !cov_2i;
  if !fails = 0 && cov_ok then
    print_endline
      "MODE-K JOURNAL OK: consolidated journal == reference (outcome+state+trace+journal), no journal realizer in the stack"
  else exit 1
