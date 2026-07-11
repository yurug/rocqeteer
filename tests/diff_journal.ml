(** Differential test for the Journal effect (IR v2 R9, adr-0013-journal-effect).

    Runs [sample_journal] (two fixed mixed-shape entries, then one entry per CONTEXT
    list element from inside a Fold body), [sample_journal_throw] (Repeat-driven
    appends, then a throw) and [sample_two] (journal-free) with adversarially-biased
    contexts at TWO different instants, comparing the reference interpreter against
    the generated direct-style code on outcome (incl. the error payload), final store
    (live bindings), trace, AND the chronological (timestamp, value) journal.

    Adversarial classes (each must be covered; coverage is ASSERTED):
      J1  empty context list           -> journal = the two fixed entries only
      J2  mixed shapes incl. NESTED DTag/DList payloads across the dval universe
      J3  large list (>= 1000)         -> per-element appends really scale with data
      J4  non-list context             -> empty fold, fixed entries only
      J5  error short-circuit          -> the k = 2 pre-throw entries survive, exactly,
                                          in Repeat order (DSome 1 then DSome 2)
      J6  ORDER under the Fold body    -> journal suffix == the input list IN ORDER
                                          (asserted against the input, not just
                                          ref==fast); a reversed list reverses it
      J7  empty run (journal-free program) -> both journals empty
      J8  sink == buffer               -> the per-entry sink callback saw exactly the
                                          buffer's entries, in order (every run)
      J9  two different now values     -> every timestamp equals the run's instant;
                                          payloads are now-independent

    Seeds are logged; every counterexample prints its seed for corpus replay.
    Reference == fast is asserted for every run. *)

module E   = Ref_extracted.EffIR
module D   = Ref_extracted.Datatypes
module S   = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260712
let rng = Random.State.make [| seed |]

let now_a = Z.zero
let now_b = Z.of_int 12345
let int64_max = Z.of_string "9223372036854775807"

(* The two fixed entries of sample_journal (theories/Samples.v). *)
let je1 = Rkv.Rval.Bytes (Bytes.of_string "j-open")
let je2 =
  Rkv.Rval.Tag (Z.of_int 5,
                Rkv.Rval.Pair (Rkv.Rval.Bytes (Bytes.of_string "SETX"),
                               Rkv.Rval.Int (Z.of_int 3)))
let jboom = Rkv.Rval.Bytes (Bytes.of_string "j-boom")

(* --- observation: outcome + sorted live store + trace + chronological journal - *)

type obs = {
  out   : (Rkv.Rval.t, Rkv.Rval.t) result;
  state : (bytes * (Rkv.Rval.t * Z.t option)) list;
  tr    : Rkv.Rval.t list;
  jr    : (Z.t * Rkv.Rval.t) list;            (* chronological *)
}

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

(* Fast side; also returns what the SINK saw (chronological) for the J8 assertion. *)
let fast_obs (fn : unit -> Rkv.Rval.t) (ctx : Rkv.Rval.t) (now : Z.t)
    : obs * (Z.t * Rkv.Rval.t) list =
  let table = Rkv.Kv.T.create 64 in
  let buf = ref [] in
  let jbuf = ref [] in
  let sunk = ref [] in
  let sink e = sunk := e :: !sunk in
  let out =
    Rkv.Env.run ctx (fun () ->
        Rkv.Trace.run buf (fun () ->
            match
              Rkv.Err.run_error (fun () ->
                  Rkv.Runtime.with_store_time_and_journal ~sink
                    ~source:(fun () -> now) table jbuf fn)
            with
            | Ok v -> Ok v
            | Error e -> Error e))
  in
  ({ out; state = Rkv.Kv.observe ~now table; tr = Rkv.Trace.contents buf;
     jr = Rkv.Journal.contents jbuf },
   List.rev !sunk)

(* --- equality + printing ----------------------------------------------------- *)

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

let show_out = function
  | Ok v -> "ret " ^ Rkv.Rval.to_string v
  | Error e -> "throw " ^ Rkv.Rval.to_string e

let show_jr l =
  "[" ^ String.concat "; "
    (List.map (fun (z, v) -> Z.to_string z ^ ":" ^ Rkv.Rval.to_string v) l) ^ "]"

let obs_eq a b =
  out_eq a.out b.out && state_eq a.state b.state && trace_eq a.tr b.tr
  && journal_eq a.jr b.jr

(* --- context generator (biased to the J-classes; nested payloads included) ---- *)

let rec gen_elem (depth : int) : Rkv.Rval.t =
  match Random.State.int rng (if depth = 0 then 6 else 9) with
  | 0 -> Rkv.Rval.Int (Z.of_int (Random.State.int rng 2001 - 1000))
  | 1 -> Rkv.Rval.Int int64_max
  | 2 ->
      Rkv.Rval.Bytes
        (Bytes.init (Random.State.int rng 6) (fun _ -> Char.chr (Random.State.int rng 256)))
  | 3 -> Rkv.Rval.Bool (Random.State.bool rng)
  | 4 -> Rkv.Rval.Unit
  | 5 -> Rkv.Rval.None
  | 6 -> Rkv.Rval.Pair (gen_elem (depth - 1), gen_elem (depth - 1))
  | 7 -> Rkv.Rval.Tag (Z.of_int (Random.State.int rng 8), gen_elem (depth - 1))
  | _ ->
      Rkv.Rval.List
        (List.init (Random.State.int rng 4) (fun _ -> gen_elem (depth - 1)))

type cls = Jempty | Jmixed | Jlarge | Jnonlist | Jsmall

let gen_ctx () : cls * Rkv.Rval.t =
  match Random.State.int rng 10 with
  | 0 -> (Jempty, Rkv.Rval.List [])
  | 1 | 2 | 3 ->
      (* J2: mixed shapes, nesting up to depth 2 *)
      let n = 1 + Random.State.int rng 8 in
      (Jmixed, Rkv.Rval.List (List.init n (fun _ -> gen_elem 2)))
  | 4 ->
      (* J3: large list, 1000-1500 elements *)
      let n = 1000 + Random.State.int rng 500 in
      (Jlarge, Rkv.Rval.List (List.init n (fun i -> Rkv.Rval.Int (Z.of_int i))))
  | 5 -> (Jnonlist, Rkv.Rval.Int (Z.of_int 3))
  | 6 -> (Jnonlist, Rkv.Rval.Bytes (Bytes.of_string "not a list"))
  | _ ->
      let n = Random.State.int rng 5 in
      (Jsmall, Rkv.Rval.List (List.init n (fun _ -> gen_elem 1)))

(* --- programs ------------------------------------------------------------------ *)

let programs : (string * E.tm * (unit -> Rkv.Rval.t)) list =
  [ ("sample_journal",       S.sample_journal,       Gen.sample_journal);
    ("sample_journal_throw", S.sample_journal_throw, Gen.sample_journal_throw);
    ("sample_two",           S.sample_two,           Gen.sample_two) ]

(* --- coverage -------------------------------------------------------------------- *)

let cov = Array.make 10 false   (* index 1..9 = J1..J9 *)

let () =
  let n = 300 in
  let fails = ref 0 in
  let drop k l =
    let rec go k l = if k = 0 then l else match l with [] -> [] | _ :: t -> go (k - 1) t in
    go k l
  in
  for _ = 1 to n do
    let (cls, ctx) = gen_ctx () in
    (match cls with
     | Jempty -> cov.(1) <- true
     | Jmixed -> cov.(2) <- true
     | Jlarge -> cov.(3) <- true
     | Jnonlist -> cov.(4) <- true
     | Jsmall -> ());
    List.iter
      (fun now ->
        List.iter
          (fun (name, term, fn) ->
            let r = ref_obs term ctx now in
            let f, sunk = fast_obs fn ctx now in
            if not (obs_eq r f) then begin
              incr fails;
              Printf.printf
                "MISMATCH %s (RSEED=%d) now=%s ctx=%s\n  ref =(%s, jr=%s)\n  fast=(%s, jr=%s)\n"
                name seed (Z.to_string now) (Rkv.Rval.to_string ctx)
                (show_out r.out) (show_jr r.jr) (show_out f.out) (show_jr f.jr)
            end;
            (* J8: the sink saw exactly the buffer, in order — every run *)
            if journal_eq f.jr sunk then cov.(8) <- true
            else begin
              incr fails;
              Printf.printf "J8 SINK FAIL %s (RSEED=%d): buffer=%s sink=%s\n"
                name seed (show_jr f.jr) (show_jr sunk)
            end;
            (* J9: every timestamp is the run's instant *)
            if List.for_all (fun (z, _) -> Z.equal z now) r.jr then begin
              if not (Z.equal now now_a) && r.jr <> [] then cov.(9) <- true
            end else begin
              incr fails;
              Printf.printf "J9 TIMESTAMP FAIL %s (RSEED=%d) now=%s: jr=%s\n"
                name seed (Z.to_string now) (show_jr r.jr)
            end;
            (* class-specific reference-side assertions *)
            (match name with
             | "sample_journal" ->
                 let payloads = List.map snd r.jr in
                 (match cls, ctx with
                  | (Jempty | Jnonlist), _ ->
                      (* J1/J4: the two fixed entries only *)
                      if not (trace_eq payloads [ je1; je2 ]) then begin
                        incr fails;
                        Printf.printf "J1/J4 FAIL (RSEED=%d): jr=%s\n" seed (show_jr r.jr)
                      end
                  | _, Rkv.Rval.List elems ->
                      (* J6: fixed prefix, then the input list IN ORDER *)
                      if trace_eq payloads (je1 :: je2 :: elems) then cov.(6) <- true
                      else begin
                        incr fails;
                        Printf.printf "J6 ORDER FAIL (RSEED=%d): jr=%s\n" seed (show_jr r.jr)
                      end
                  | _ -> ())
             | "sample_journal_throw" ->
                 (* J5: throw payload + exactly the k = 2 pre-throw entries, in
                    Repeat order (the counter reads 1 then 2) *)
                 let expect =
                   [ Rkv.Rval.Some (Rkv.Rval.Int Z.one);
                     Rkv.Rval.Some (Rkv.Rval.Int (Z.of_int 2)) ] in
                 (match r.out with
                  | Error e when Rkv.Rval.equal e jboom
                                 && trace_eq (List.map snd r.jr) expect ->
                      cov.(5) <- true
                  | _ ->
                      incr fails;
                      Printf.printf "J5 FAIL (RSEED=%d): out=%s jr=%s\n"
                        seed (show_out r.out) (show_jr r.jr))
             | "sample_two" ->
                 (* J7: a journal-free program leaves both journals empty *)
                 if r.jr = [] && f.jr = [] then cov.(7) <- true
                 else begin
                   incr fails;
                   Printf.printf "J7 FAIL (RSEED=%d): ref=%s fast=%s\n"
                     seed (show_jr r.jr) (show_jr f.jr)
                 end
             | _ -> ()))
          programs)
      [ now_a; now_b ];
    (* J9 companion: payloads are now-independent (only timestamps move) *)
    let ra = ref_obs S.sample_journal ctx now_a
    and rb = ref_obs S.sample_journal ctx now_b in
    if not (trace_eq (List.map snd ra.jr) (List.map snd rb.jr)) then begin
      incr fails;
      Printf.printf "J9 PAYLOAD FAIL (RSEED=%d): a=%s b=%s\n"
        seed (show_jr ra.jr) (show_jr rb.jr)
    end;
    ignore (drop 0 [])
  done;

  (* J6 companion: a concrete list and its REVERSE yield reversed journal suffixes
     (order is genuinely observable, not accidentally symmetric). *)
  let l = [ Rkv.Rval.Int Z.one; Rkv.Rval.Int (Z.of_int 2); Rkv.Rval.Int (Z.of_int 3) ] in
  let fwd = ref_obs S.sample_journal (Rkv.Rval.List l) now_a in
  let bwd = ref_obs S.sample_journal (Rkv.Rval.List (List.rev l)) now_a in
  let suffix o = List.filteri (fun i _ -> i >= 2) (List.map snd o.jr) in
  if not (trace_eq (suffix fwd) l && trace_eq (suffix bwd) (List.rev l)
          && not (trace_eq (suffix fwd) (suffix bwd)))
  then begin
    incr fails;
    Printf.printf "J6 REVERSE FAIL (RSEED=%d): fwd=%s bwd=%s\n"
      seed (show_jr fwd.jr) (show_jr bwd.jr)
  end;

  let cov_ok = cov.(1) && cov.(2) && cov.(3) && cov.(4) && cov.(5)
               && cov.(6) && cov.(7) && cov.(8) && cov.(9) in
  Printf.printf
    "rounds=%d programs=%d instants=2 fails=%d\n\
     coverage: J1(empty)=%b J2(mixed-nested)=%b J3(large-1000+)=%b J4(non-list)=%b\n\
     J5(short-circuit/Repeat-order)=%b J6(Fold-order)=%b J7(empty-run)=%b\n\
     J8(sink==buffer)=%b J9(two-instants)=%b\n"
    n (List.length programs) !fails
    cov.(1) cov.(2) cov.(3) cov.(4) cov.(5) cov.(6) cov.(7) cov.(8) cov.(9);
  if !fails = 0 && cov_ok then
    print_endline
      "JOURNAL DIFFERENTIAL OK: reference == fast (outcome+state+trace+journal) over \
       J1-J9; order asserted under Repeat and Fold; sink == buffer; timestamps = run \
       instant at two instants; coverage asserted"
  else begin
    if not cov_ok then
      print_endline "JOURNAL COVERAGE GAP: a required class (J1-J9) was never exercised";
    exit 1
  end
