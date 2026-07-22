(** Differential test for the SOCKET family (C4, adr-0018) — REAL loopback TCP.

    Record-and-replay (Runtime_Sock_script_faithful): the harness scripts each
    connection's bytes, drives them through actual TCP as a forked CLIENT process
    (connect → send all → shutdown-write → read response to EOF → close: the
    ONE-SHOT half-close contract, by construction), runs the GENERATED server
    ([sample_http] / [sample_http_big], via Rkv.Sockio over a real listener) in
    the parent, and replays the SAME script through the extracted REFERENCE
    ([observe_sock]).  Compared per connection, in order: the response bytes the
    client actually received == the reference transcript's outputs
    (== [SockIO.http_prog_correct]'s spec, by the proven theorem).

    Classes (ASSERTED): S1 route hit · S2 miss (404) · S3 malformed (400) ·
    S4 request-line CRLF straddling the recv-chunk boundary · S5 NUL/high bytes
    in the path · S6 empty request · S7 the exhausted VALUE path (a
    pre-closed listener, the empty script: every accept no-ops) · S8 big instance at 512-boundaries ·
    FI1 short-recv interposition (unchanged) · FI2 the timeout backstop (a
    client that never half-closes -> `Environmental, LOUD, not a hang).

    Seeded and reproducible (RSEED). *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260723
let rng = Random.State.make [| seed |]
let fails = ref 0

(* --- the route table (shared by both sides) ------------------------------------ *)

let table : (string * string) list =
  [ ("/", "home"); ("/x", "payload"); ("/nul\x00", "nulled");
    ("/big", String.make 2000 'B') ]

let ctx_rval : Rkv.Rval.t =
  Rkv.Rval.List
    (List.map
       (fun (p, b) ->
         Rkv.Rval.Pair
           (Rkv.Rval.Bytes (Bytes.of_string p), Rkv.Rval.Bytes (Bytes.of_string b)))
       table)

(* --- reference side ------------------------------------------------------------- *)

let ref_outputs (term : E.tm) (script : string list) : string list =
  let coq_script =
    Coqconv.coq_list_of
      (List.map (fun r -> Coqconv.bytes_to_ascii_list (Bytes.of_string r)) script)
  in
  let _, transcript =
    match E.observe_sock (Coqconv.dval_of_rval ctx_rval) coq_script term with
    | D.Coq_pair (o, t) -> (o, t)
  in
  Coqconv.list_of_coq transcript
  |> List.map (fun p ->
         match p with
         | D.Coq_pair (_, D.Coq_pair (_, out)) ->
             Bytes.to_string (Coqconv.ascii_list_to_bytes out))

(* --- live side: fork clients, run the generated server ------------------------- *)

let mk_listener () =
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt sock Unix.SO_REUSEADDR true;
  Unix.bind sock (Unix.ADDR_INET (Unix.inet_addr_loopback, 0));
  Unix.listen sock 16;
  let port =
    match Unix.getsockname sock with
    | Unix.ADDR_INET (_, p) -> p
    | _ -> failwith "diff_sock: no port"
  in
  (sock, port)

let read_all fd =
  let buf = Buffer.create 256 in
  let chunk = Bytes.create 4096 in
  let rec go () =
    match Unix.read fd chunk 0 4096 with
    | 0 -> ()
    | n -> Buffer.add_subbytes buf chunk 0 n; go ()
  in
  go (); Buffer.contents buf

let write_all fd (s : string) =
  let b = Bytes.of_string s in
  let rec go off =
    if off < Bytes.length b then
      go (off + Unix.write fd b off (Bytes.length b - off))
  in
  go 0

(** The child: drive every scripted connection sequentially (one-shot, half-close),
    record the responses to [outfile], then exit. *)
let run_clients (port : int) (script : string list) (outfile : string) : unit =
  let oc = open_out_bin outfile in
  List.iter
    (fun req ->
      let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      Unix.connect s (Unix.ADDR_INET (Unix.inet_addr_loopback, port));
      write_all s req;
      Unix.shutdown s Unix.SHUTDOWN_SEND;          (* the half-close contract *)
      let resp = read_all s in
      Unix.close s;
      Printf.fprintf oc "%d\n%s" (String.length resp) resp)
    script;
  close_out oc

let read_recorded (outfile : string) : string list =
  let ic = open_in_bin outfile in
  let rec go acc =
    match input_line ic with
    | n ->
        let len = int_of_string n in
        let b = really_input_string ic len in
        go (b :: acc)
    | exception End_of_file -> List.rev acc
  in
  let r = go [] in
  close_in ic; r

(** Run the generated server over a real listener against forked scripted
    clients; [close_after] connections, then close the listener so the server's
    remaining fuel takes the exhausted-VALUE path. *)
let live_outputs ?(sys = Rkv.Sockio.real_sys) (fn : unit -> 'a)
    (script : string list) :
    (string list, Rkv.Sockio.error) result =
  let listener, port = mk_listener () in
  let outfile = Filename.temp_file "rocqeteer_sock" ".out" in
  match Unix.fork () with
  | 0 ->
      (* child: the clients; then closing our end is enough — the parent closes
         the listener itself after the child exits *)
      Unix.close listener;
      (try run_clients port script outfile with _ -> ());
      exit 0
  | pid ->
      let table = Rkv.Kv.T.create 8 in
      (* HARNESS CONTRACT: [length script] equals the sample's accept fuel, so
         the server's loop exits exactly when the last client is served and the
         accept never blocks on a missing (n+1)-th connection.  The exhausted-
         VALUE path is exercised separately (S7: a pre-closed listener and the
         empty script). *)
      let result =
        Rkv.Env.run ctx_rval (fun () ->
            Rkv.Runtime.with_store_and_time ~source:(fun () -> Z.zero) table
              (fun () ->
                Rkv.Sockio.run_checked ~sys ~timeout:5.0 ~listener (fun () ->
                    Rkv.Err.run_error fn)))
      in
      ignore (Unix.waitpid [] pid);
      Unix.close listener;
      (match result with
       | Ok (Ok _) -> Ok (read_recorded outfile)
       | Ok (Error e) ->
           Error (`Unexpected_exception
                    ("program threw: " ^ Rkv.Rval.to_string e))
       | Error e -> Error e)

let check name (term : E.tm) (fn : unit -> 'a) (script : string list) =
  let r = ref_outputs term script in
  match live_outputs fn script with
  | Ok l ->
      if l <> r then begin
        incr fails;
        Printf.printf "SOCK MISMATCH %s (RSEED=%d): %d conns\n" name seed
          (List.length script);
        List.iteri
          (fun i (a, b) ->
            if a <> b then
              Printf.printf "  conn %d:\n   ref =%S\n   live=%S\n" (i + 1) b a)
          (List.combine l r)
      end
  | Error e ->
      incr fails;
      Printf.printf "SOCK LIVE ERROR %s: %s\n" name (Rkv.Sockio.string_of_error e)

(* --- scripts -------------------------------------------------------------------- *)

let get path = "GET " ^ path ^ " HTTP/1.0\r\n\r\n"

let gen_junk () =
  let n = Random.State.int rng 30 in
  String.init n (fun _ -> Char.chr (32 + Random.State.int rng 95))

(* --- main ------------------------------------------------------------------------ *)

let () =
  (* sample_http: fuel_conns = 3 — scripts of exactly 3 (the harness contract) *)
  check "hit/miss/bad" S.sample_http Gen.sample_http
    [ get "/x"; get "/nope"; "junk" ];                       (* S1 S2 S3 *)
  check "straddle" S.sample_http Gen.sample_http
    [ "GET / HTTP1.0\r\n\r\n"; get "/"; get "/big" ];       (* S4 + big body *)
  check "nul-path" S.sample_http Gen.sample_http
    [ get "/nul\x00"; ""; get "/x" ];                        (* S5 S6 *)
  for _ = 1 to 20 do
    check "random" S.sample_http Gen.sample_http
      [ (if Random.State.bool rng then get "/x" else gen_junk ());
        (if Random.State.bool rng then get "/" else get "/nope");
        gen_junk () ]
  done;
  (* S8: the big instance (fuel_conns = 16, ml = 512): 16 scripted connections
     around the 512-chunk boundary *)
  check "big-boundaries" S.sample_http_big Gen.sample_http_big
    (List.init 16 (fun i ->
         let pad = String.make (505 + (i mod 4)) 'P' in
         get ("/" ^ pad)));
  (* S7: pre-closed listener + empty script — the whole fuel takes the
     exhausted-VALUE path on BOTH sides (transcripts empty) *)
  (let listener, _port = mk_listener () in
   Unix.close listener;
   let table = Rkv.Kv.T.create 8 in
   let r = ref_outputs S.sample_http [] in
   let result =
     Rkv.Env.run ctx_rval (fun () ->
         Rkv.Runtime.with_store_and_time ~source:(fun () -> Z.zero) table
           (fun () ->
             Rkv.Sockio.run_checked ~timeout:5.0 ~listener (fun () ->
                 Rkv.Err.run_error (fun () -> Gen.sample_http ()))))
   in
   match result, r with
   | Ok (Ok _), [] -> ()
   | _ -> incr fails; print_endline "S7 FAIL: exhausted path diverged");
  (* FI1: short-recv interposition — Runtime_SockRecv_full at the seam *)
  (let starved =
     { Rkv.Sockio.real_sys with
       Rkv.Sockio.sys_recv =
         (fun fd b o l -> Unix.recv fd b o (min 1 l) []) }
   in
   let script = [ get "/x"; get "/"; "junk" ] in
   let r = ref_outputs S.sample_http script in
   match live_outputs ~sys:starved Gen.sample_http script with
   | Ok l when l = r -> ()
   | _ -> incr fails; print_endline "FI1 FAIL: short-recv changed the outcome");
  (* FI2: the timeout backstop — a client that never half-closes must abort
     LOUDLY as Environmental, not hang *)
  (let listener, port = mk_listener () in
   match Unix.fork () with
   | 0 ->
       Unix.close listener;
       let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
       Unix.connect s (Unix.ADDR_INET (Unix.inet_addr_loopback, port));
       write_all s "GET /x HTT";                            (* ... and stall *)
       Unix.sleepf 10.0;
       (try Unix.close s with _ -> ());
       exit 0
   | pid ->
       let table = Rkv.Kv.T.create 8 in
       let result =
         Rkv.Env.run ctx_rval (fun () ->
             Rkv.Runtime.with_store_and_time ~source:(fun () -> Z.zero) table
               (fun () ->
                 Rkv.Sockio.run_checked ~timeout:1.0 ~listener (fun () ->
                     Rkv.Err.run_error (fun () -> Gen.sample_http ()))))
       in
       (try Unix.kill pid Sys.sigkill with _ -> ());
       (try ignore (Unix.waitpid [] pid) with _ -> ());
       Unix.close listener;
       (match result with
        | Error (`Environmental _) -> ()
        | _ ->
            incr fails;
            print_endline "FI2 FAIL: stalled client did not abort environmentally"));
  Printf.printf "SOCK checks done, fails=%d\n" !fails;
  if !fails = 0 then
    print_endline
      "SOCK DIFFERENTIAL OK: reference == generated over real loopback TCP (record-and-replay); one-shot contract, short-recv seam, and the timeout backstop hold"
  else exit 1
