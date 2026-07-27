(** Concurrent-server differential (C5, adr-0019): the NATIVE concurrent HTTP server
    (acceptor + worker fibers under the Effect.Deep scheduler, nesting the real socket
    realizer) vs the extracted sequential reference [observe_sock http_prog].

    This composes the two realizers validated separately — [diff_sched] (the scheduler
    bookkeeping) and [diff_sock] (the socket ops over real TCP) — into the end-to-end
    claim: certified concurrency, scheduled run-to-completion, serves EXACTLY the proven
    sequential transcript (SockIO.http_prog_correct, transferred by
    SchedHttp.drv_concurrent_matches).

    Harness (the diff_sock pattern): fork a child that drives 3 one-shot clients
    sequentially (send, half-close, read-to-EOF); the parent runs the concurrent server
    over a real loopback listener; compare the responses the clients received to the
    reference transcript.  Accept fuel is 3 (drv_acceptor) = the client count — the
    server's loops exit exactly when the last client is served (no blocking on a missing
    4th connection). *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let fails = ref 0

let table : (string * string) list =
  [ ("/", "home"); ("/x", "payload"); ("/nul\x00", "nulled") ]

let ctx_rval : Rkv.Rval.t =
  Rkv.Rval.List
    (List.map
       (fun (p, b) ->
         Rkv.Rval.Pair
           (Rkv.Rval.Bytes (Bytes.of_string p), Rkv.Rval.Bytes (Bytes.of_string b)))
       table)

(* --- reference side (the sequential server, = the proven concurrent transcript) --- *)

let ref_outputs (script : string list) : string list =
  let coq_script =
    Coqconv.coq_list_of
      (List.map (fun r -> Coqconv.bytes_to_ascii_list (Bytes.of_string r)) script)
  in
  let _, transcript =
    match E.observe_sock (Coqconv.dval_of_rval ctx_rval) coq_script S.sample_http with
    | D.Coq_pair (o, t) -> (o, t)
  in
  Coqconv.list_of_coq transcript
  |> List.map (fun p ->
         match p with
         | D.Coq_pair (_, D.Coq_pair (_, out)) ->
             Bytes.to_string (Coqconv.ascii_list_to_bytes out))

(* --- harness ---------------------------------------------------------------------- *)

let mk_listener () =
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt sock Unix.SO_REUSEADDR true;
  Unix.bind sock (Unix.ADDR_INET (Unix.inet_addr_loopback, 0));
  Unix.listen sock 16;
  let port =
    match Unix.getsockname sock with
    | Unix.ADDR_INET (_, p) -> p
    | _ -> failwith "no port"
  in
  (sock, port)

let read_all fd =
  let buf = Buffer.create 256 and chunk = Bytes.create 4096 in
  let rec go () =
    match Unix.read fd chunk 0 4096 with
    | 0 -> ()
    | n -> Buffer.add_subbytes buf chunk 0 n; go ()
  in
  go (); Buffer.contents buf

let write_all fd (s : string) =
  let b = Bytes.of_string s in
  let rec go off =
    if off < Bytes.length b then go (off + Unix.write fd b off (Bytes.length b - off))
  in
  go 0

let run_clients (port : int) (script : string list) (outfile : string) : unit =
  let oc = open_out_bin outfile in
  List.iter
    (fun req ->
      let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      Unix.connect s (Unix.ADDR_INET (Unix.inet_addr_loopback, port));
      write_all s req;
      Unix.shutdown s Unix.SHUTDOWN_SEND;
      let resp = read_all s in
      Unix.close s;
      Printf.fprintf oc "%d\n%s" (String.length resp) resp)
    script;
  close_out oc

let read_recorded (outfile : string) : string list =
  let ic = open_in_bin outfile in
  let rec go acc =
    match input_line ic with
    | n -> let len = int_of_string n in
           let b = really_input_string ic len in go (b :: acc)
    | exception End_of_file -> List.rev acc
  in
  let r = go [] in close_in ic; r

(* The CONCURRENT server: acceptor + worker fibers under Rkv.Sched, nested inside the
   real socket / store / env / err realizers. Same run-to-completion schedule the tool
   uses. *)
let acceptor_fiber () = Gen.drv_acceptor (); Rkv.Rval.Unit
let worker_fiber () = Gen.drv_worker (); Rkv.Rval.Unit
(* [acceptor; worker; worker] per connection — real blocking accept requires the worker
   to fully serve a connection before the next accept (see tools/rhttpd_conc.ml). *)
let schedule = List.concat (List.init 6 (fun _ -> [ Z.one; Z.of_int 2; Z.of_int 2 ]))

let live_outputs (script : string list) : (string list, string) result =
  let listener, port = mk_listener () in
  let outfile = Filename.temp_file "rocqeteer_conc" ".out" in
  match Unix.fork () with
  | 0 ->
      Unix.close listener;
      (try run_clients port script outfile with _ -> ());
      exit 0
  | pid ->
      let table_kv = Rkv.Kv.T.create 8 in
      let result =
        Rkv.Env.run ctx_rval (fun () ->
            Rkv.Runtime.with_store_and_time ~source:(fun () -> Z.zero) table_kv
              (fun () ->
                Rkv.Sockio.run_checked ~timeout:5.0 ~listener (fun () ->
                    Rkv.Err.run_error (fun () ->
                        Rkv.Sched.run ~chans:[ Z.zero ] ~next_fib:(Z.of_int 3)
                          ~next_chan:Z.one
                          ~bodies:(fun _ () -> Rkv.Rval.Unit)
                          ~schedule
                          [ (Z.one, acceptor_fiber); (Z.of_int 2, worker_fiber) ]))))
      in
      ignore (Unix.waitpid [] pid);
      Unix.close listener;
      let ret =
        match result with
        | Ok (Ok sched_res) -> (
            match sched_res with
            | Rkv.Sched.Completed _ -> Ok (read_recorded outfile)
            | Rkv.Sched.Stuck (live, _) ->
                Error
                  (Printf.sprintf "scheduler stuck: fibers %s live"
                     (String.concat "," (List.map Z.to_string live))))
        | Ok (Error e) -> Error ("a fiber threw: " ^ Rkv.Rval.to_string e)
        | Error e -> Error (Rkv.Sockio.string_of_error e)
      in
      (try Sys.remove outfile with _ -> ());
      ret

let check name (script : string list) =
  let r = ref_outputs script in
  match live_outputs script with
  | Ok l ->
      if l <> r then begin
        incr fails;
        Printf.printf "CONC MISMATCH %s: %d conns\n" name (List.length script);
        List.iteri
          (fun i (a, b) ->
            if a <> b then
              Printf.printf "  conn %d:\n   ref =%S\n   live=%S\n" (i + 1) b a)
          (List.combine l r)
      end
  | Error e ->
      incr fails;
      Printf.printf "CONC LIVE ERROR %s: %s\n" name e

let get path = "GET " ^ path ^ " HTTP/1.0\r\n\r\n"

let () =
  (* drv_acceptor/drv_worker fuel = 3 -> scripts of exactly 3 (harness contract). *)
  check "hit/miss/bad" [ get "/x"; get "/nope"; "junk" ];      (* 200 · 404 · 400 *)
  check "nul/empty/hit" [ get "/nul\x00"; ""; get "/" ];       (* NUL path · empty · 200 *)
  check "all-hit" [ get "/"; get "/x"; get "/nul\x00" ];
  check "all-bad" [ "junk"; "GET"; "\r\n\r\n" ];
  Printf.printf "CONC SCHED-HTTP: %d cases, %d fails\n" 4 !fails;
  if !fails = 0 then
    print_endline
      "CONC SCHED-HTTP OK: native concurrent server (acceptor+worker fibers, scheduled) \
       == sequential reference over real TCP"
  else exit 1
