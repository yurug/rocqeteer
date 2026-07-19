(** Differential test for the FILE family (C3, adr-0017) — through REAL files.

    Three-way on the wc samples: reference interpreter (pure in-world fsys) ==
    generated fast code (Rkv.Fileio over actual syscalls in a scratch dir) ==
    coreutils (`wc -c`).  Plus the write path (sample_file_rw: the bytes on DISK
    must equal the reference file region), the modeled-error VALUES
    (sample_file_missing), and the adr-0017 seam checks:
      FI1 short-read interposition (sys_read capped at 1 byte)  -> unchanged
          (Runtime_FileRead_full witnessed at the seam)
      FI2 injected EIO                                          -> `Environmental
      FI3 aliased operands via symlink                          -> REFUSED
          (Runtime_FS_distinct_inodes)
      FI4 symlink operand                                       -> FOLLOWED
          (count of the target — the cat/wc semantics)
      FI5 external modification between open and close          -> DETECTED
          (Runtime_FS_open_inode_stable)

    Corpus classes (ASSERTED): F1 empty · F2 NUL bytes · F3 non-UTF8 high bytes ·
    F4 no-trailing-newline · F5 small chunk boundaries (k*3±1 for sample_wc,
    cap 24) · F6 big chunk boundaries (k*512±1 for sample_wc_big, cap 32768) ·
    F7 huge single line.  Seeded and reproducible (RSEED). *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

let seed = try int_of_string (Sys.getenv "RSEED") with _ -> 20260722
let rng = Random.State.make [| seed |]

let fails = ref 0
let scratch_root =
  let d =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "rocqeteer_diff_file_%d" (Unix.getpid ()))
  in
  (try Unix.mkdir d 0o700 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  d

let case_ctr = ref 0

let fresh_dir () =
  incr case_ctr;
  let d = Filename.concat scratch_root (string_of_int !case_ctr) in
  Unix.mkdir d 0o700;
  d

let write_file dir name (contents : bytes) =
  let oc = open_out_bin (Filename.concat dir name) in
  output_bytes oc contents;
  close_out oc

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let b = really_input_string ic n in
  close_in ic;
  Bytes.of_string b

(* --- reference side ------------------------------------------------------------ *)

type obs = {
  out : (Rkv.Rval.t, Rkv.Rval.t) result;
  fls : (string * bytes) list;          (* final file region, sorted *)
}

let ref_obs (term : E.tm) (name : string) (contents : bytes option) : obs =
  let fl =
    match contents with
    | None -> E.M.empty
    | Some c ->
        E.M.add (Coqconv.coq_string_of_bytes (Bytes.of_string name))
          (Coqconv.bytes_to_ascii_list c) E.M.empty
  in
  let ctx = Coqconv.dval_of_rval (Rkv.Rval.Bytes (Bytes.of_string name)) in
  let oc, files =
    match E.observe_file ctx fl term with D.Coq_pair (o, fs) -> (o, fs)
  in
  let out =
    match oc with
    | E.ORet v -> Ok (Coqconv.rval_of_dval v)
    | E.OErr e -> Error (Coqconv.rval_of_dval e)
  in
  let fls =
    Coqconv.list_of_coq files
    |> List.map (fun p ->
           match p with
           | D.Coq_pair (k, cs) ->
               (Bytes.to_string (Coqconv.bytes_of_coq_string k),
                Coqconv.ascii_list_to_bytes cs))
    |> List.sort compare
  in
  { out; fls }

(* --- fast side ------------------------------------------------------------------ *)

let fast_out ?(sys = Rkv.Fileio.real_sys) (fn : unit -> Rkv.Rval.t)
    (dir : string) (operand : string) :
    ((Rkv.Rval.t, Rkv.Rval.t) result, Rkv.Fileio.error) result =
  let table = Rkv.Kv.T.create 8 in
  Rkv.Env.run (Rkv.Rval.Bytes (Bytes.of_string operand)) (fun () ->
      Rkv.Runtime.with_store_and_time ~source:(fun () -> Z.zero) table (fun () ->
          Rkv.Fileio.run_checked ~sys ~dir (fun () ->
              Rkv.Err.run_error fn)))

let dir_listing dir =
  Sys.readdir dir |> Array.to_list |> List.sort compare
  |> List.map (fun n -> (n, read_file (Filename.concat dir n)))

let out_eq a b =
  match a, b with
  | Ok x, Ok y | Error x, Error y -> Rkv.Rval.equal x y
  | _ -> false

let show_out = function
  | Ok v -> "ret " ^ Rkv.Rval.to_string v
  | Error e -> "throw " ^ Rkv.Rval.to_string e

let coreutils_count path : Z.t =
  let ic = Unix.open_process_in ("wc -c < " ^ Filename.quote path) in
  let line = input_line ic in
  ignore (Unix.close_process_in ic);
  Z.of_string (String.trim line)

let check_wc (label : string) (term : E.tm) (fn : unit -> Rkv.Rval.t)
    (contents : bytes) =
  let dir = fresh_dir () in
  write_file dir "f" contents;
  let r = ref_obs term "f" (Some contents) in
  let f = fast_out fn dir "f" in
  let expected = Rkv.Rval.Int (Z.of_int (Bytes.length contents)) in
  (match r.out, f with
   | Ok rv, Ok (Ok fv)
     when Rkv.Rval.equal rv fv && Rkv.Rval.equal rv expected -> ()
   | _, _ ->
       incr fails;
       Printf.printf "FILE MISMATCH %s (RSEED=%d) size=%d\n  ref=%s fast=%s\n"
         label seed (Bytes.length contents) (show_out r.out)
         (match f with
          | Ok o -> show_out o
          | Error e -> "ENV " ^ Rkv.Fileio.string_of_error e));
  (* three-way: coreutils *)
  let wc = coreutils_count (Filename.concat dir "f") in
  if not (Z.equal wc (Z.of_int (Bytes.length contents))) then (
    incr fails;
    Printf.printf "COREUTILS MISMATCH %s: wc -c says %s\n" label (Z.to_string wc))

(* --- corpus generators ---------------------------------------------------------- *)

let gen_byte () =
  match Random.State.int rng 5 with
  | 0 -> '\x00'
  | 1 -> Char.chr (128 + Random.State.int rng 128)
  | 2 -> '\n'
  | _ -> Char.chr (32 + Random.State.int rng 95)

let gen_contents (n : int) : bytes =
  Bytes.init n (fun _ -> gen_byte ())

(* --- main ------------------------------------------------------------------------ *)

let () =
  (* F5: every small size around the 3-byte chunk boundaries, cap 8*3 = 24 *)
  for n = 0 to 24 do
    check_wc "sample_wc" S.sample_wc Gen.sample_wc (gen_contents n)
  done;
  (* F6: big chunk boundaries for the tool instance (512-byte chunks, cap 32 KiB) *)
  List.iter
    (fun n -> check_wc "sample_wc_big" S.sample_wc_big Gen.sample_wc_big
                (gen_contents n))
    [ 0; 1; 511; 512; 513; 1024; 8191; 8192; 20000; 32767; 32768 ];
  (* F7: a huge single line (no newline at all) *)
  check_wc "sample_wc_big" S.sample_wc_big Gen.sample_wc_big
    (Bytes.make 20001 'x');
  (* random rounds across the classes *)
  for _ = 1 to 200 do
    let n = Random.State.int rng 25 in
    check_wc "sample_wc" S.sample_wc Gen.sample_wc (gen_contents n)
  done;
  for _ = 1 to 50 do
    let n = Random.State.int rng 32769 in
    check_wc "sample_wc_big" S.sample_wc_big Gen.sample_wc_big (gen_contents n)
  done;

  (* F8: the write path — bytes on DISK == the reference file region *)
  (let dir = fresh_dir () in
   let r = ref_obs S.sample_file_rw "unused" None in
   let f = fast_out Gen.sample_file_rw dir "unused" in
   (match r.out, f with
    | Ok rv, Ok (Ok fv) when Rkv.Rval.equal rv fv -> ()
    | _ ->
        incr fails;
        Printf.printf "RW OUTCOME MISMATCH: ref=%s fast=%s\n" (show_out r.out)
          (match f with
           | Ok o -> show_out o
           | Error e -> "ENV " ^ Rkv.Fileio.string_of_error e));
   let disk = dir_listing dir in
   let refl = List.map (fun (k, c) -> (k, c)) r.fls in
   if disk <> refl then (
     incr fails;
     Printf.printf "RW DISK MISMATCH: disk=[%s] ref=[%s]\n"
       (String.concat ";" (List.map fst disk))
       (String.concat ";" (List.map fst refl))));

  (* F9: the modeled-error VALUES flow identically (no file, no abort) *)
  (let dir = fresh_dir () in
   let r = ref_obs S.sample_file_missing "absent" None in
   let f = fast_out Gen.sample_file_missing dir "absent" in
   match r.out, f with
   | Ok rv, Ok (Ok fv) when Rkv.Rval.equal rv fv -> ()
   | _ ->
       incr fails;
       Printf.printf "MISSING MISMATCH: ref=%s fast=%s\n" (show_out r.out)
         (match f with
          | Ok o -> show_out o
          | Error e -> "ENV " ^ Rkv.Fileio.string_of_error e));

  (* FI1: short-read interposition — Runtime_FileRead_full at the seam *)
  (let dir = fresh_dir () in
   let contents = gen_contents 23 in
   write_file dir "f" contents;
   let starved =
     { Rkv.Fileio.real_sys with
       Rkv.Fileio.sys_read =
         (fun fd buf off len -> Unix.read fd buf off (min 1 len)) }
   in
   let r = ref_obs S.sample_wc "f" (Some contents) in
   let f = fast_out ~sys:starved Gen.sample_wc dir "f" in
   match r.out, f with
   | Ok rv, Ok (Ok fv) when Rkv.Rval.equal rv fv -> ()
   | _ ->
       incr fails;
       print_endline "FI1 FAIL: short-read interposition changed the outcome");

  (* FI2: injected EIO -> `Environmental, loudly *)
  (let dir = fresh_dir () in
   write_file dir "f" (gen_contents 10);
   let broken =
     { Rkv.Fileio.real_sys with
       Rkv.Fileio.sys_read =
         (fun _ _ _ _ -> raise (Unix.Unix_error (Unix.EIO, "read", ""))) }
   in
   match fast_out ~sys:broken Gen.sample_wc dir "f" with
   | Error (`Environmental _) -> ()
   | _ -> incr fails; print_endline "FI2 FAIL: EIO did not surface as Environmental");

  (* FI3: aliased operands are REFUSED (Runtime_FS_distinct_inodes) *)
  (let dir = fresh_dir () in
   write_file dir "a" (gen_contents 5);
   Unix.symlink "a" (Filename.concat dir "b");
   match
     Rkv.Fileio.run_checked ~dir (fun () ->
         let r1 = Rkv.Fileio.open_ (Bytes.of_string "a") (Rkv.Rval.Int Z.zero) in
         let r2 = Rkv.Fileio.open_ (Bytes.of_string "b") (Rkv.Rval.Int Z.zero) in
         Rkv.Rval.Pair (r1, r2))
   with
   | Error (`Environmental _) -> ()
   | _ -> incr fails; print_endline "FI3 FAIL: aliased open was not refused");

  (* FI4: a symlink OPERAND is followed (count of the target) *)
  (let dir = fresh_dir () in
   let contents = gen_contents 17 in
   write_file dir "target" contents;
   Unix.symlink "target" (Filename.concat dir "link");
   let r = ref_obs S.sample_wc "link" (Some contents) in
   let f = fast_out Gen.sample_wc dir "link" in
   match r.out, f with
   | Ok rv, Ok (Ok fv) when Rkv.Rval.equal rv fv -> ()
   | _ -> incr fails; print_endline "FI4 FAIL: symlink operand not followed");

  (* FI5: external modification between open and close is DETECTED *)
  (let dir = fresh_dir () in
   write_file dir "f" (gen_contents 10);
   match
     Rkv.Fileio.run_checked ~dir (fun () ->
         match Rkv.Fileio.open_ (Bytes.of_string "f") (Rkv.Rval.Int Z.zero) with
         | Rkv.Rval.Tag (_, fd) ->
             let oc =
               open_out_gen [ Open_append ] 0o644 (Filename.concat dir "f")
             in
             output_string oc "external!";
             close_out oc;
             Rkv.Fileio.close_ fd
         | v -> v)
   with
   | Error (`Environmental _) -> ()
   | _ ->
       incr fails;
       print_endline "FI5 FAIL: external modification not detected at close");

  Printf.printf
    "FILE cases=%d fails=%d | classes: F1-F7 corpora (boundaries, NUL, high bytes, huge), F8 disk==reference, F9 modeled errors, FI1-FI5 seam checks\n"
    !case_ctr !fails;
  if !fails = 0 then
    print_endline
      "FILE DIFFERENTIAL OK: reference == generated == coreutils through real files; seam checks (full-read, EIO, aliasing, symlink-follow, change-detection) hold"
  else exit 1
