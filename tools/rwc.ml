(* rwc — the C3 application (adr-0017): a proven byte-count tool.
   The counting core is the Rocq program Samples.wc_prog (theorem
   FileIO.wc_prog_correct: count = file size for files up to 64*512 bytes),
   emitted by the certified pipeline into generated/prog0_generated.ml
   (sample_wc_big). This wrapper is UNTRUSTED shell glue per adr-0017 §2:
   argv -> the OAsk context, outcome -> exit code, environmental failures
   -> loud stderr. *)
let () =
  match Sys.argv with
  | [| _; path |] ->
      let dir = Filename.dirname path and base = Filename.basename path in
      let table = Rkv.Kv.T.create 4 in
      let result =
        Rkv.Env.run (Rkv.Rval.Bytes (Bytes.of_string base)) (fun () ->
            Rkv.Runtime.with_store_and_time
              ~source:(fun () -> Z.zero) table (fun () ->
                Rkv.Fileio.run_checked ~dir (fun () ->
                    Rkv.Err.run_error (fun () ->
                        Generated.Prog0_generated.sample_wc_big ()))))
      in
      (match result with
       | Ok (Ok (Rkv.Rval.Int n)) ->
           Printf.printf "%s %s\n" (Z.to_string n) path
       | Ok (Ok v) ->
           Printf.eprintf "rwc: unexpected result %s\n" (Rkv.Rval.to_string v);
           exit 3
       | Ok (Error payload) ->
           (* the program THREW: for a missing operand this is the modeled
              Tag(1, 2) ENOENT value (theories/Samples.v wc_prog) *)
           Printf.eprintf "rwc: cannot open %s: %s\n" path
             (Rkv.Rval.to_string payload);
           exit 1
       | Error e ->
           Printf.eprintf "rwc: %s\n" (Rkv.Fileio.string_of_error e);
           exit 2)
  | _ ->
      prerr_endline "usage: rwc FILE  (byte count; proven core, <= 32 KiB)";
      exit 64
