(** Runtime file-I/O effect and deep handler (C3, adr-0017).

    The realizer of the file family over [Unix.openfile/read/write/close] — no C
    stubs.  Semantics mirror the reference [handle_file] exactly on the MODELED
    surface:
      open_ path (Int 0): read — ENOENT is the VALUE Tag(1, Int 2); symlinks are
        FOLLOWED (a file tool's operand semantics, cat/wc-style; adr-0017 seam);
      open_ path (Int 1): write-truncate (creates/empties);
      read fd maxlen: EXACTLY min(maxlen, remaining) bytes — the FULL-READ loop
        discharges POSIX short reads/EINTR (Runtime_FileRead_full); the EMPTY chunk
        is EOF; unknown/wrong-mode fds are the VALUE Tag(1, Int 9);
      write fd bytes: append, FULL-WRITE loop (Runtime_FileWrite_full);
      close_ fd: Bool (was open; double-close = false).
    Malformed arguments raise [Rval.Stuck], mirroring the reference [Dstuck] (the
    generated-code convention).

    THE SEAM (adr-0017 Reasoning model): everything ENVIRONMENTAL — EACCES, EIO,
    ENOSPC, aliasing, external modification — is an [Env_failure] carrying the
    tagged payload Tag(66, Bytes reason), surfaced as a typed error at the checked
    boundary, never a silent wrong answer.  Two runtime CHECKS narrow the named
    assumptions:
      - Runtime_FS_distinct_inodes: at each open, the fd is fstat'ed and its
        (st_dev, st_ino) compared against the open set — aliased operands are
        REFUSED (the cp "same file" posture);
      - Runtime_FS_open_inode_stable (detection only): read fds record (size,
        mtime) at open and re-fstat at close — a detected external modification is
        an Env_failure (the rsync/editor posture: detection, not prevention).

    Tests interpose on the [sys] record (short reads, injected errors) — the Time
    [source] pattern applied to syscalls. *)

type error =
  [ `Unhandled_effect of string
  | `Unexpected_exception of string
  | `Environmental of Rval.t ]

let string_of_error = function
  | `Unhandled_effect s -> "unhandled effect: " ^ s
  | `Unexpected_exception s -> "unexpected exception: " ^ s
  | `Environmental v -> "environmental failure: " ^ Rval.to_string v

exception Env_failure of Rval.t

let env_fail (reason : string) : 'a =
  raise (Env_failure (Rval.Tag (Z.of_int 66, Rval.Bytes (Bytes.of_string reason))))

(** The syscall layer — interposable for fault injection (the Time.source pattern). *)
type sys = {
  sys_open  : string -> Unix.open_flag list -> Unix.file_perm -> Unix.file_descr;
  sys_read  : Unix.file_descr -> bytes -> int -> int -> int;
  sys_write : Unix.file_descr -> bytes -> int -> int -> int;
  sys_close : Unix.file_descr -> unit;
  sys_fstat : Unix.file_descr -> Unix.stats;
}

let real_sys : sys = {
  sys_open  = Unix.openfile;
  sys_read  = Unix.read;
  sys_write = Unix.write;
  sys_close = Unix.close;
  sys_fstat = Unix.fstat;
}

(* Tupled effect constructors, hidden by the .mli (audit C1 discipline). *)
type _ Effect.t +=
  | FOpen  : (bytes * Rval.t) -> Rval.t Effect.t
  | FRead  : (Rval.t * Rval.t) -> Rval.t Effect.t
  | FWrite : (Rval.t * Rval.t) -> Rval.t Effect.t
  | FClose : Rval.t -> Rval.t Effect.t

let open_ p m = Effect.perform (FOpen (p, m))
let read f n = Effect.perform (FRead (f, n))
let write f b = Effect.perform (FWrite (f, b))
let close_ f = Effect.perform (FClose f)

(* One open descriptor: the OS fd, its mode (0 read / 1 write), and for read fds the
   (dev, ino, size, mtime) snapshot backing the two runtime checks. *)
type slot = {
  osfd : Unix.file_descr;
  mode : int;
  dev_ino : int * int;
  snap : (int * float) option;      (* (size, mtime) at open; read fds only *)
}

module ZTbl = Hashtbl.Make (struct
  type t = Z.t
  let equal = Z.equal
  let hash z = Hashtbl.hash (Z.to_string z)
end)

(** The full-read loop (Runtime_FileRead_full): exactly [want] bytes unless EOF
    arrives first — short reads and EINTR are discharged HERE, never observable. *)
let read_full (s : sys) (fd : Unix.file_descr) (want : int) : bytes =
  let buf = Bytes.create want in
  let rec go (off : int) =
    if off = want then want
    else
      match s.sys_read fd buf off (want - off) with
      | 0 -> off                                   (* EOF *)
      | n -> go (off + n)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> go off
      | exception Unix.Unix_error (e, _, _) ->
          env_fail ("read: " ^ Unix.error_message e)
  in
  let got = go 0 in
  Bytes.sub buf 0 got

(** The full-write loop (Runtime_FileWrite_full). *)
let write_full (s : sys) (fd : Unix.file_descr) (b : bytes) : unit =
  let len = Bytes.length b in
  let rec go (off : int) =
    if off < len then
      match s.sys_write fd b off (len - off) with
      | n -> go (off + n)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> go off
      | exception Unix.Unix_error (e, _, _) ->
          env_fail ("write: " ^ Unix.error_message e)
  in
  go 0

let tag_enoent = Rval.Tag (Z.of_int 1, Rval.Int (Z.of_int 2))
let tag_ebadf = Rval.Tag (Z.of_int 1, Rval.Int (Z.of_int 9))

(** Deep handler.  [dir] roots relative paths (tests run in scratch directories);
    [sys] is the interposable syscall layer.  Each continuation resumes once. *)
let run ?(sys = real_sys) ~(dir : string) (f : unit -> 'a) : 'a =
  let table : slot ZTbl.t = ZTbl.create 8 in
  let next_fd = ref (Z.of_int 3) in
  let in_dir p = Filename.concat dir p in
  let alias_check (di : int * int) =
    ZTbl.iter
      (fun _ s -> if s.dev_ino = di then env_fail "aliased paths (same dev/ino)")
      table
  in
  match f () with
  | v -> v
  | effect FOpen (p, m), kont ->
      let path = Bytes.to_string p in
      let mode =
        match m with
        | Rval.Int z when Z.equal z Z.zero -> 0
        | Rval.Int z when Z.equal z Z.one -> 1
        | _ -> raise Rval.Stuck
      in
      let result =
        if mode = 0 then
          match sys.sys_open (in_dir path) [ Unix.O_RDONLY ] 0 with
          | osfd ->
              let st = sys.sys_fstat osfd in
              let di = (st.Unix.st_dev, st.Unix.st_ino) in
              alias_check di;
              let fd = !next_fd in
              next_fd := Z.succ !next_fd;
              ZTbl.replace table fd
                { osfd; mode; dev_ino = di;
                  snap = Some (st.Unix.st_size, st.Unix.st_mtime) };
              Rval.Tag (Z.zero, Rval.Int fd)
          | exception Unix.Unix_error (Unix.ENOENT, _, _) -> tag_enoent
          | exception Unix.Unix_error (e, _, _) ->
              env_fail ("open: " ^ Unix.error_message e)
        else
          match
            sys.sys_open (in_dir path)
              [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC ] 0o644
          with
          | osfd ->
              let st = sys.sys_fstat osfd in
              let di = (st.Unix.st_dev, st.Unix.st_ino) in
              alias_check di;
              let fd = !next_fd in
              next_fd := Z.succ !next_fd;
              ZTbl.replace table fd { osfd; mode; dev_ino = di; snap = None };
              Rval.Tag (Z.zero, Rval.Int fd)
          | exception Unix.Unix_error (e, _, _) ->
              env_fail ("open: " ^ Unix.error_message e)
      in
      Effect.Deep.continue kont result
  | effect FRead (fv, nv), kont ->
      let fd = match fv with Rval.Int z -> z | _ -> raise Rval.Stuck in
      let maxlen = match nv with Rval.Int z -> z | _ -> raise Rval.Stuck in
      if Z.leq maxlen Z.zero then raise Rval.Stuck;
      let result =
        match ZTbl.find_opt table fd with
        | Some s when s.mode = 0 ->
            Rval.Bytes (read_full sys s.osfd (Z.to_int maxlen))
        | _ -> tag_ebadf
      in
      Effect.Deep.continue kont result
  | effect FWrite (fv, bv), kont ->
      let fd = match fv with Rval.Int z -> z | _ -> raise Rval.Stuck in
      let b = match bv with Rval.Bytes b -> b | _ -> raise Rval.Stuck in
      let result =
        match ZTbl.find_opt table fd with
        | Some s when s.mode = 1 ->
            write_full sys s.osfd b;
            Rval.Unit
        | _ -> tag_ebadf
      in
      Effect.Deep.continue kont result
  | effect FClose fv, kont ->
      let fd = match fv with Rval.Int z -> z | _ -> raise Rval.Stuck in
      let result =
        match ZTbl.find_opt table fd with
        | Some s ->
            (* Runtime_FS_open_inode_stable, DETECTION half: a read fd whose size or
               mtime changed since open was externally modified mid-run. *)
            (match s.snap with
             | Some (sz, mt) ->
                 let st = sys.sys_fstat s.osfd in
                 if st.Unix.st_size <> sz || st.Unix.st_mtime <> mt then
                   env_fail "file changed during run (size/mtime)"
             | None -> ());
            (match sys.sys_close s.osfd with
             | () -> ()
             | exception Unix.Unix_error (e, _, _) ->
                 env_fail ("close: " ^ Unix.error_message e));
            ZTbl.remove table fd;
            Rval.Bool true
        | None -> Rval.Bool false
      in
      Effect.Deep.continue kont result

let run_checked ?(sys = real_sys) ~dir f =
  try Ok (run ~sys ~dir f) with
  | Env_failure v -> Error (`Environmental v)
  | Effect.Unhandled _ as e -> Error (`Unhandled_effect (Printexc.to_string e))
  | e -> Error (`Unexpected_exception (Printexc.to_string e))
