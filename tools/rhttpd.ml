(* rhttpd — the C4 application (adr-0018): a proven sequential HTTP/1.0 server.
   The serving core is the Rocq program Samples.http_prog (theorem
   SockIO.http_prog_correct: every connection's response equals the reference
   response function of its request), emitted by the certified pipeline
   (sample_http_big: 16 one-shot connections, 512-byte chunks, 32 KiB requests).
   This wrapper is UNTRUSTED shell glue per adr-0018 §3: it owns bind/listen,
   packs the route table into the OAsk context, and maps outcomes to exit codes.
   Clients must follow the one-shot contract: send, half-close, read to EOF
   (e.g. tests/diff_sock.ml's clients). *)
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
      let listener = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      Unix.setsockopt listener Unix.SO_REUSEADDR true;
      Unix.bind listener
        (Unix.ADDR_INET (Unix.inet_addr_loopback, int_of_string port));
      Unix.listen listener 16;
      Printf.printf "rhttpd: serving 16 one-shot connections on 127.0.0.1:%s\n%!"
        port;
      let table = Rkv.Kv.T.create 8 in
      let result =
        Rkv.Env.run ctx (fun () ->
            Rkv.Runtime.with_store_and_time ~source:(fun () -> Z.zero) table
              (fun () ->
                Rkv.Sockio.run_checked ~timeout:30.0 ~listener (fun () ->
                    Rkv.Err.run_error (fun () ->
                        Generated.Prog0_generated.sample_http_big ()))))
      in
      Unix.close listener;
      (match result with
       | Ok (Ok _) -> print_endline "rhttpd: done"
       | Ok (Error e) ->
           Printf.eprintf "rhttpd: program threw %s\n" (Rkv.Rval.to_string e);
           exit 1
       | Error e ->
           Printf.eprintf "rhttpd: %s\n" (Rkv.Sockio.string_of_error e);
           exit 2)
  | _ ->
      prerr_endline
        "usage: rhttpd PORT [path body]...  (proven core; one-shot HTTP/1.0)";
      exit 64
