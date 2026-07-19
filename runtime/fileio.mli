(** Public interface of the file-I/O realizer (C3, adr-0017).

    Effect constructors hidden (audit C1 discipline): generated code calls the
    curried wrappers only.  Results mirror the reference [handle_file] dvals:
    [open_]: Tag(0, Int fd) | Tag(1, Int 2) (ENOENT value, read mode);
    [read]: Bytes chunk (EMPTY = EOF) | Tag(1, Int 9) (EBADF value);
    [write]: Unit | Tag(1, Int 9); [close_]: Bool (double-close = false).
    Malformed arguments raise [Rval.Stuck] (the generated-code Dstuck convention).

    Environmental failures (EACCES/EIO/..., refused aliasing per
    Runtime_FS_distinct_inodes, detected external modification per
    Runtime_FS_open_inode_stable) surface ONLY at the checked boundary as
    [`Environmental (Tag(66, Bytes reason))]. *)

type error =
  [ `Unhandled_effect of string
  | `Unexpected_exception of string
  | `Environmental of Rval.t ]

val string_of_error : error -> string

(** Interposable syscall layer — fault-injection seam (the Time.source pattern). *)
type sys = {
  sys_open  : string -> Unix.open_flag list -> Unix.file_perm -> Unix.file_descr;
  sys_read  : Unix.file_descr -> bytes -> int -> int -> int;
  sys_write : Unix.file_descr -> bytes -> int -> int -> int;
  sys_close : Unix.file_descr -> unit;
  sys_fstat : Unix.file_descr -> Unix.stats;
}

val real_sys : sys

(** Curried public wrappers — the only way to perform a file operation. *)
val open_ : bytes -> Rval.t -> Rval.t
val read : Rval.t -> Rval.t -> Rval.t
val write : Rval.t -> Rval.t -> Rval.t
val close_ : Rval.t -> Rval.t

(** Deep handler; [dir] roots relative paths (tests use scratch directories). *)
val run : ?sys:sys -> dir:string -> (unit -> 'a) -> 'a

val run_checked : ?sys:sys -> dir:string -> (unit -> 'a) -> ('a, error) result
