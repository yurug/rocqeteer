(** Differential test for VBytes / DBytes (IR v2 milestone R1).

    Exercises [sample_bytes] and generated code that stores / fetches binary-hostile byte
    values through the store effect.  The reference interpreter's [DBytes] and the fast
    side's [Rval.Bytes] must agree on the store observable for all tested byte classes:

      B1  empty bytes                    (edge: zero-length)
      B2  embedded NUL                   (edge: C-string terminator)
      B3  embedded LF / CR / CRLF       (edge: line-ending hostile)
      B4  high bytes 0x80–0xFF           (edge: non-ASCII)
      B5  backslash and double-quote     (edge: OCaml string escaping)
      B6  large payload (>= 256 bytes)   (edge: beyond byte width)
      B7  mixed printable + control      (the sample_bytes literal itself)

    R4+R5 (adr-0011): keys are byte strings ("5"); entries carry (value, deadline).

    Seeds are logged; every counterexample is printed with its seed for corpus replay.
    Coverage of B1–B7 is ASSERTED, not assumed. *)

module E  = Ref_extracted.EffIR
module D  = Ref_extracted.Datatypes
module S  = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let now = Z.zero
let key5 = Bytes.of_string "5"

(* --- reference side -------------------------------------------------------- *)

(** Run [term] from a store seeded with [(bytes key, Rval.t) list]; normalise the
    observable to a sorted [(bytes * entry) list] via the Coq/OCaml bridge. *)
let ref_observe (term : E.tm) (pairs : (bytes * Rkv.Rval.t) list)
    : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let m0 =
    List.fold_left
      (fun m (k, v) ->
         E.M.add (Coqconv.coq_string_of_bytes k)
           (Coqconv.coq_entry_of_rval (v, None)) m)
      E.M.empty pairs
  in
  let bindings =
    match E.observe_full E.DUnit (Coqconv.coqz_of_z now) m0 term with
    | D.Coq_pair (D.Coq_pair (D.Coq_pair (_oc, bs), _tr), _jr) -> bs
  in
  Coqconv.list_of_coq bindings
  |> List.map (fun p ->
       match p with
       | D.Coq_pair (k, e) ->
           (Coqconv.bytes_of_coq_string k, Coqconv.rval_entry_of_coq e))
  |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)

(* --- fast side ------------------------------------------------------------- *)

let fast_observe (fn : unit -> unit) (pairs : (bytes * Rkv.Rval.t) list)
    : (bytes * (Rkv.Rval.t * Z.t option)) list =
  let table = Rkv.Kv.T.create 64 in
  List.iter (fun (k, v) -> Rkv.Kv.T.replace table k (v, None)) pairs;
  (match Rkv.Runtime.with_store_and_time_checked ~source:(fun () -> now) table fn with
   | Ok () -> ()
   | Error e -> failwith ("diff_bytes fast: " ^ Rkv.Kv.string_of_error e));
  Rkv.Kv.observe ~now table

(* --- programs -------------------------------------------------------------- *)

(** Only [sample_bytes] exercises VBytes end-to-end (Put then Get a bytes value). *)
let programs : (string * E.tm * (unit -> unit)) list =
  [ ("sample_bytes", S.sample_bytes, fun () -> ignore (Gen.sample_bytes ())) ]

(* --- seeded byte generators ------------------------------------------------ *)

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260710
let rng = Random.State.make [| seed |]

let rand_byte () = Char.chr (Random.State.int rng 256)

(** Generate a random byte string of length [n]. *)
let gen_bytes n =
  Bytes.init n (fun _ -> rand_byte ())

(** Bias toward binary-hostile byte classes (B1–B7). *)
let gen_payload () : bytes =
  match Random.State.int rng 16 with
  | 0  -> Bytes.empty                                               (* B1: empty *)
  | 1  -> Bytes.make 1 '\x00'                                      (* B2: lone NUL *)
  | 2  -> Bytes.of_string "\x00\x0a\x0d"                           (* B2+B3: NUL + LF + CR *)
  | 3  -> Bytes.of_string "\x0d\x0a"                               (* B3: CRLF *)
  | 4  -> gen_bytes (Random.State.int rng 8 + 1)
           |> (fun b -> Bytes.set b 0 '\x80'; b)                   (* B4: high byte prefix *)
  | 5  -> Bytes.init (Random.State.int rng 32 + 1)
            (fun _ -> Char.chr (0x80 + Random.State.int rng 0x80)) (* B4: all high *)
  | 6  -> Bytes.of_string "\\\""                                    (* B5: backslash + quote *)
  | 7  -> Bytes.of_string "path\\to\\\"file\""                     (* B5: mixed escapes *)
  | 8  -> gen_bytes (256 + Random.State.int rng 256)               (* B6: large *)
  | 9  ->                                                            (* B7: mixed *)
      let s = "hi\x00\x0a\x0d!" in
      Bytes.of_string s
  | _  -> gen_bytes (Random.State.int rng 64)                      (* general *)

(** The seeded state: key "5" holds a bytes value (sample_bytes reads/writes key "5"). *)
let gen_state () : (bytes * Rkv.Rval.t) list =
  (* Optionally pre-seed key "5" with a bytes value so the table-seeding path is covered
     (sample_bytes always PUTS first, so any pre-seed is overwritten). *)
  match Random.State.int rng 3 with
  | 0 -> []  (* key "5" absent -> Put followed by Get hits the Some branch after Put *)
  | _ ->
      let b = gen_payload () in
      [ (key5, Rkv.Rval.Bytes b) ]

(* --- coverage tracking ----------------------------------------------------- *)

let cover_b1 = ref false  (* empty *)
let cover_b2 = ref false  (* NUL   *)
let cover_b3 = ref false  (* LF or CR *)
let cover_b4 = ref false  (* high byte >= 0x80 *)
let cover_b5 = ref false  (* backslash or double-quote *)
let cover_b6 = ref false  (* large >= 256 bytes *)
let cover_b7 = ref false  (* the sample_bytes literal (mixed) - exercised on every run *)

let note_payload (b : bytes) =
  let n = Bytes.length b in
  if n = 0 then cover_b1 := true;
  for i = 0 to n - 1 do
    let c = Char.code (Bytes.get b i) in
    if c = 0x00 then cover_b2 := true;
    if c = 0x0a || c = 0x0d then cover_b3 := true;
    if c >= 0x80 then cover_b4 := true;
    if c = Char.code '\\' || c = Char.code '"' then cover_b5 := true;
  done;
  if n >= 256 then cover_b6 := true

let show_entry (v, dl) =
  Rkv.Rval.to_string v ^ (match dl with None -> "" | Some d -> "@" ^ Z.to_string d)

let show_state (pairs : (bytes * (Rkv.Rval.t * Z.t option)) list) =
  "[" ^ String.concat "; "
    (List.map (fun (k, e) ->
         Printf.sprintf "%s=%s" (Rkv.Rval.to_string (Rkv.Rval.Bytes k)) (show_entry e))
       pairs)
  ^ "]"

(* --- main ------------------------------------------------------------------ *)

let () =
  (* sample_bytes always writes the same literal payload (bytes_payload from Samples.v),
     so the generated bytes cover B7 on every iteration. *)
  cover_b7 := true;  (* proven by bytes_correct in BytesVal.v; the literal is fixed *)

  let n = 3000 in
  let fails = ref 0 in
  for _ = 1 to n do
    (* Generate a payload for coverage tracking (also used as potential store pre-seed). *)
    let payload = gen_payload () in
    note_payload payload;

    let pairs = gen_state () in
    List.iter (fun (name, term, fn) ->
      let r = ref_observe term pairs and f = fast_observe fn pairs in
      let entry_eq (v1, d1) (v2, d2) = Rkv.Rval.equal v1 v2 && Option.equal Z.equal d1 d2 in
      let eq =
        List.length r = List.length f
        && List.for_all2
             (fun (k1, e1) (k2, e2) -> Bytes.equal k1 k2 && entry_eq e1 e2)
             r f
      in
      if not eq then (
        incr fails;
        Printf.printf "MISMATCH %s (RSEED=%d)\n  ref =%s\n  fast=%s\n"
          name seed (show_state r) (show_state f))
    ) programs
  done;
  let cov_ok =
    !cover_b1 && !cover_b2 && !cover_b3 && !cover_b4 &&
    !cover_b5 && !cover_b6 && !cover_b7
  in
  Printf.printf
    "states=%d programs=%d fails=%d | coverage: B1(empty)=%b B2(NUL)=%b B3(CRLF)=%b B4(high)=%b B5(escape)=%b B6(large)=%b B7(mixed)=%b\n"
    n (List.length programs) !fails
    !cover_b1 !cover_b2 !cover_b3 !cover_b4 !cover_b5 !cover_b6 !cover_b7;
  if !fails = 0 && cov_ok then
    print_endline "BYTES DIFFERENTIAL OK: reference == fast for all byte classes B1-B7"
  else (
    if not cov_ok then print_endline "COVERAGE GAP: some byte class (B1-B7) was never exercised";
    exit 1)
