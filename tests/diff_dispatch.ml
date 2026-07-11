(** Dispatch differential test (IR v2 R2, adr-0008-general-match).

    [sample_dispatch] reads the context (OAsk) and dispatches on PBytes literal patterns:
      "GET" -> ORet (DInt 1),  "SET" -> ORet (DInt 2),  default -> ORet (DInt 0).

    This test runs the reference interpreter and the generated direct-style code over random
    DBytes / Rval.Bytes context values and asserts they produce identical outcomes.

    Coverage classes:
      D1  exact "GET" bytes             -> expected outcome 1
      D2  exact "SET" bytes             -> expected outcome 2
      D3  other bytes (default branch)  -> expected outcome 0
      D4  empty bytes                   -> default (binary-hostile edge)
      D5  non-ASCII bytes               -> default (B4 edge)

    Seeds are logged; every counterexample prints its seed for corpus replay. *)

module E   = Ref_extracted.EffIR
module D   = Ref_extracted.Datatypes
module S   = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

(* Reference: run sample_dispatch with a Bytes context; extract the outcome. *)
let ref_outcome (ctx_bytes : bytes) : Rkv.Rval.t =
  let coq_ctx = E.DBytes (Coqconv.bytes_to_ascii_list ctx_bytes) in
  match E.run_top coq_ctx (Coqconv.coqz_of_z Z.zero) S.sample_dispatch with
  | D.Coq_pair (E.ORet v, _) -> Coqconv.rval_of_dval v
  | D.Coq_pair (E.OErr e, _) ->
      failwith ("diff_dispatch ref error: " ^ Rkv.Rval.to_string (Coqconv.rval_of_dval e))

(* Fast: run the generated sample_dispatch under the Env handler (no KV needed). *)
let fast_outcome (ctx_bytes : bytes) : Rkv.Rval.t =
  let result = ref Rkv.Rval.None in
  Rkv.Env.run (Rkv.Rval.Bytes ctx_bytes) (fun () ->
    result := Gen.sample_dispatch ());
  !result

(* Encode "GET" and "SET" as bytes (must match the Rocq ASCII literals in Samples.v). *)
let get_bytes = Bytes.of_string "GET"
let set_bytes = Bytes.of_string "SET"

(* --- seeded generator -------------------------------------------------------- *)

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260710
let rng = Random.State.make [| seed |]

let gen_ctx () : bytes =
  match Random.State.int rng 16 with
  | 0  -> get_bytes                                           (* D1: exact "GET" *)
  | 1  -> set_bytes                                           (* D2: exact "SET" *)
  | 2  -> Bytes.empty                                         (* D4: empty bytes *)
  | 3  -> Bytes.make 1 '\x00'                                 (* D5: NUL byte *)
  | 4  -> Bytes.init (1 + Random.State.int rng 32)
             (fun _ -> Char.chr (0x80 + Random.State.int rng 0x80)) (* D5: high bytes *)
  | _  ->                                                     (* D3: random other bytes *)
      let n = Random.State.int rng 8 in
      Bytes.init n (fun _ -> Char.chr (Random.State.int rng 256))

(* --- coverage tracking ------------------------------------------------------ *)

let cover_get     = ref false
let cover_set     = ref false
let cover_default = ref false
let cover_empty   = ref false
let cover_nonascii = ref false

let note_ctx (b : bytes) =
  if Bytes.equal b get_bytes      then cover_get     := true
  else if Bytes.equal b set_bytes then cover_set     := true
  else                                 cover_default := true;
  if Bytes.length b = 0 then cover_empty := true;
  Bytes.iter (fun c -> if Char.code c >= 0x80 then cover_nonascii := true) b

(* --- main ------------------------------------------------------------------- *)

let () =
  let n = 3000 in
  let fails = ref 0 in
  let get_ok = ref 0 and set_ok = ref 0 and def_ok = ref 0 in
  for _ = 1 to n do
    let ctx = gen_ctx () in
    note_ctx ctx;
    let r = ref_outcome ctx and f = fast_outcome ctx in
    let eq = Rkv.Rval.equal r f in
    if not eq then (
      incr fails;
      Printf.printf "MISMATCH (RSEED=%d) ctx=%s\n  ref=%s\n  fast=%s\n"
        seed (Rkv.Rval.to_string (Rkv.Rval.Bytes ctx))
        (Rkv.Rval.to_string r) (Rkv.Rval.to_string f))
    else (
      (* Validate the expected outcome for known contexts. *)
      if Bytes.equal ctx get_bytes && Rkv.Rval.equal r (Rkv.Rval.Int (Z.of_int 1)) then incr get_ok;
      if Bytes.equal ctx set_bytes && Rkv.Rval.equal r (Rkv.Rval.Int (Z.of_int 2)) then incr set_ok;
      if (not (Bytes.equal ctx get_bytes) && not (Bytes.equal ctx set_bytes))
         && Rkv.Rval.equal r (Rkv.Rval.Int Z.zero) then incr def_ok)
  done;
  let cov_ok = !cover_get && !cover_set && !cover_default && !cover_empty && !cover_nonascii in
  Printf.printf
    "states=%d fails=%d | branch-hits: GET->1=%d SET->2=%d default->0=%d | coverage: D1(GET)=%b D2(SET)=%b D3(default)=%b D4(empty)=%b D5(nonascii)=%b\n"
    n !fails !get_ok !set_ok !def_ok
    !cover_get !cover_set !cover_default !cover_empty !cover_nonascii;
  if !fails = 0 && cov_ok then
    print_endline "DISPATCH DIFFERENTIAL OK: reference == fast for all dispatch branches; coverage D1-D5 asserted"
  else (
    if not cov_ok then print_endline "DISPATCH COVERAGE GAP: a required class (D1-D5) was never exercised";
    exit 1)
