(* rhttpd_conc — the C5 application (adr-0019): a proven CONCURRENT HTTP/1.0 server.

   The certified concurrency differentiator made real: two fibers — an ACCEPTOR and a
   WORKER (Samples.drv_acceptor / drv_worker, emitted by the codegen; SchedHttp.v proves
   that under a run-to-completion schedule they recover Samples.http_prog's transcript,
   = SockIO.http_prog_correct) — run under the OCaml Effect.Deep scheduler realizer
   (Rkv.Sched) over the SAME native TCP the sequential rhttpd uses.

   Handler nesting (outer -> inner): Env (route table) -> Store (the per-connection
   buffer) -> Sockio (real TCP) -> Err (throw) -> Sched (the 5 conc ops).  A fiber's
   socket/store/throw effects propagate OUT of the scheduler handler (which returns None
   for them) to the enclosing realizer — the pattern diff_sched already exercises for
   Trace.  The injected schedule is run-to-completion ([1;2] alternation): the acceptor
   accepts one connection and hands it to the worker, which serves it fully before the
   next accept, so the transcript equals the sequential server's.

   Untrusted shell glue (adr-0018 §3): owns bind/listen, packs the route table, maps
   outcomes to exit codes.  Accept fuel is 3 (drv_acceptor) — the harness contract:
   exactly 3 one-shot clients (send, half-close, read to EOF). *)

module Gen = Generated.Prog0_generated

(* Fibers as (unit -> Rval.t): the generated Repeat loops return unit; the fiber's
   outcome is ORet DUnit, so wrap to Rval.Unit. *)
let acceptor_fiber () = Gen.drv_acceptor (); Rkv.Rval.Unit
let worker_fiber () = Gen.drv_worker (); Rkv.Rval.Unit

(* Run-to-completion per connection: [acceptor; worker; worker].  With REAL blocking
   accept the acceptor must NOT try the next accept until the worker has fully served
   the current connection (else it blocks for a client that will not connect until the
   previous one is answered).  The worker needs two slots per connection — one to take
   the channel value (the scheduler DELIVERS a recv and defers its continuation, matching
   the reference sched_one), one to run the handler.  Generously long; extra slots on
   completed fibers are no-ops. *)
let schedule : Z.t list =
  List.concat (List.init 6 (fun _ -> [ Z.one; Z.of_int 2; Z.of_int 2 ]))

(* Bind a loopback listener, failing GRACEFULLY (message + exit code, no backtrace) on
   a bad/out-of-range port, an address already in use, or a privileged port. *)
let bind_listener (label : string) (port_s : string) : Unix.file_descr =
  let port =
    match int_of_string_opt port_s with
    | Some p when p >= 0 && p <= 65535 -> p
    | _ ->
        Printf.eprintf "%s: invalid port %S (expected 0-65535)\n" label port_s;
        exit 64
  in
  let listener = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt listener Unix.SO_REUSEADDR true;
  (try
     Unix.bind listener (Unix.ADDR_INET (Unix.inet_addr_loopback, port));
     Unix.listen listener 16
   with Unix.Unix_error (e, _, _) ->
     (try Unix.close listener with _ -> ());
     Printf.eprintf "%s: cannot listen on 127.0.0.1:%d — %s\n" label port
       (Unix.error_message e);
     exit 74);
  listener

let () =
  match Array.to_list Sys.argv with
  | _ :: port :: routes when List.length routes mod 2 = 0 ->
      let rec pair = function
        | [] -> []
        | p :: b :: r -> (p, b) :: pair r
        | _ -> []
      in
      let ctx =
        Rkv.Rval.List
          (List.map
             (fun (p, b) ->
               Rkv.Rval.Pair
                 (Rkv.Rval.Bytes (Bytes.of_string p),
                  Rkv.Rval.Bytes (Bytes.of_string b)))
             (pair routes))
      in
      let listener = bind_listener "rhttpd_conc" port in
      Printf.printf
        "rhttpd_conc: serving 3 one-shot connections (acceptor+worker fibers) on \
         127.0.0.1:%s\n%!"
        port;
      let table = Rkv.Kv.T.create 8 in
      let result =
        Rkv.Env.run ctx (fun () ->
            Rkv.Runtime.with_store_and_time ~source:(fun () -> Z.zero) table
              (fun () ->
                Rkv.Sockio.run_checked ~timeout:30.0 ~listener (fun () ->
                    Rkv.Err.run_error (fun () ->
                        Rkv.Sched.run ~chans:[ Z.zero ] ~next_fib:(Z.of_int 3)
                          ~next_chan:Z.one
                          ~bodies:(fun _ () -> Rkv.Rval.Unit)
                          ~schedule
                          [ (Z.one, acceptor_fiber);
                            (Z.of_int 2, worker_fiber) ]))))
      in
      Unix.close listener;
      (match result with
       | Ok (Ok sched_res) ->
           Printf.printf "rhttpd_conc: done — %s\n"
             (Rkv.Sched.string_of_result sched_res)
       | Ok (Error e) ->
           Printf.eprintf "rhttpd_conc: a fiber threw %s\n" (Rkv.Rval.to_string e);
           exit 1
       | Error e ->
           Printf.eprintf "rhttpd_conc: %s\n" (Rkv.Sockio.string_of_error e);
           exit 2)
  | _ ->
      prerr_endline
        "usage: rhttpd_conc PORT [path body]...  (proven concurrent core; 3 one-shot \
         HTTP/1.0 connections)";
      exit 64
