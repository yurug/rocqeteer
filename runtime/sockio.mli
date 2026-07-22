(** Public interface of the socket realizer (C4, adr-0018).

    ONE-SHOT half-close-driven connections; results mirror the reference
    [handle_sock] dvals: [accept]: Tag(0, Int conn) | Tag(1, Int 11) (input done —
    the wrapper closed the listener); [recv]: Bytes chunk (EMPTY = half-close) |
    Tag(1, Int 9); [send]: Unit | Tag(1, Int 9); [close_conn]: Bool.  Malformed
    arguments raise [Rval.Stuck].  Environmental failures — send/recv errors, the
    RECEIVE-TIMEOUT liveness backstop firing on a client that never half-closes —
    surface only at the checked boundary as [`Environmental (Tag(66, reason))]. *)

type error =
  [ `Unhandled_effect of string
  | `Unexpected_exception of string
  | `Environmental of Rval.t ]

val string_of_error : error -> string

type sys = {
  sys_accept : Unix.file_descr -> Unix.file_descr * Unix.sockaddr;
  sys_recv   : Unix.file_descr -> bytes -> int -> int -> int;
  sys_send   : Unix.file_descr -> bytes -> int -> int -> int;
  sys_close  : Unix.file_descr -> unit;
}

val real_sys : sys

val accept : unit -> Rval.t
val recv : Rval.t -> Rval.t -> Rval.t
val send : Rval.t -> Rval.t -> Rval.t
val close_conn : Rval.t -> Rval.t

(** [listener] must already be listening (wrapper-owned setup, adr-0018 §3);
    [timeout] arms the per-connection receive backstop. *)
val run : ?sys:sys -> ?timeout:float -> listener:Unix.file_descr
  -> (unit -> 'a) -> 'a

val run_checked : ?sys:sys -> ?timeout:float -> listener:Unix.file_descr
  -> (unit -> 'a) -> ('a, error) result
