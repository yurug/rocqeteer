(** Runtime socket effect and deep handler (C4, adr-0018).

    The realizer of the socket family over Unix TCP sockets — no C stubs.
    ONE-SHOT, HALF-CLOSE-DRIVEN connections (adr-0018 §1): the client sends its
    whole request and shuts down its write side; [recv] loops to [maxlen] or EOF
    (Runtime_SockRecv_full — terminating BECAUSE of the protocol contract), so
    the reference's deterministic [file_chunk] is realized verbatim.

    Listener setup is WRAPPER-OWNED ([run] takes an already-listening socket).
    Script exhaustion (the reference's Tag(1,11) EAGAIN value) is realized by the
    wrapper CLOSING the listener when the input is done: an accept on a closed
    listener returns the value, mirroring the reference — a blocking accept is
    simply a pending connection.

    The LIVENESS BACKSTOP (adr-0018 §7): a receive timeout on every accepted
    socket converts a client that never half-closes into a loud environmental
    abort — the server never hangs silently.  Environmental failures surface as
    [`Environmental (Tag(66, reason))] at the checked boundary only. *)

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

(** Interposable syscall layer (fault-injection seam, the fileio pattern). *)
type sys = {
  sys_accept : Unix.file_descr -> Unix.file_descr * Unix.sockaddr;
  sys_recv   : Unix.file_descr -> bytes -> int -> int -> int;
  sys_send   : Unix.file_descr -> bytes -> int -> int -> int;
  sys_close  : Unix.file_descr -> unit;
}

let real_sys : sys = {
  sys_accept = Unix.accept;
  sys_recv = (fun fd b o l -> Unix.recv fd b o l []);
  sys_send = (fun fd b o l -> Unix.send fd b o l []);
  sys_close = Unix.close;
}

type _ Effect.t +=
  | Accept : unit -> Rval.t Effect.t
  | Recv : (Rval.t * Rval.t) -> Rval.t Effect.t
  | Send : (Rval.t * Rval.t) -> Rval.t Effect.t
  | CloseConn : Rval.t -> Rval.t Effect.t

let accept () = Effect.perform (Accept ())
let recv c n = Effect.perform (Recv (c, n))
let send c b = Effect.perform (Send (c, b))
let close_conn c = Effect.perform (CloseConn c)

module ZTbl = Hashtbl.Make (struct
  type t = Z.t
  let equal = Z.equal
  let hash z = Hashtbl.hash (Z.to_string z)
end)

let tag_exhausted = Rval.Tag (Z.of_int 1, Rval.Int (Z.of_int 11))
let tag_ebadf = Rval.Tag (Z.of_int 1, Rval.Int (Z.of_int 9))

(** The full-recv loop (Runtime_SockRecv_full): exactly [want] bytes unless the
    peer's half-close arrives first.  EINTR retried; a timeout is the liveness
    backstop firing. *)
let recv_full (s : sys) (fd : Unix.file_descr) (want : int) : bytes =
  let buf = Bytes.create want in
  let rec go off =
    if off = want then want
    else
      match s.sys_recv fd buf off (want - off) with
      | 0 -> off
      | n -> go (off + n)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> go off
      | exception Unix.Unix_error ((Unix.EAGAIN | Unix.EWOULDBLOCK), _, _) ->
          env_fail "recv timeout (client never half-closed?)"
      | exception Unix.Unix_error (e, _, _) ->
          env_fail ("recv: " ^ Unix.error_message e)
  in
  let got = go 0 in
  Bytes.sub buf 0 got

let send_full (s : sys) (fd : Unix.file_descr) (b : bytes) : unit =
  let len = Bytes.length b in
  let rec go off =
    if off < len then
      match s.sys_send fd b off (len - off) with
      | n -> go (off + n)
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> go off
      | exception Unix.Unix_error (e, _, _) ->
          env_fail ("send: " ^ Unix.error_message e)
  in
  go 0

(** Deep handler.  [listener] is already listening (wrapper-owned setup);
    [timeout] arms the per-connection receive backstop (seconds). *)
let run ?(sys = real_sys) ?(timeout = 5.0) ~(listener : Unix.file_descr)
    (f : unit -> 'a) : 'a =
  let table : Unix.file_descr ZTbl.t = ZTbl.create 8 in
  let next_conn = ref Z.one in
  match f () with
  | v -> v
  | effect Accept (), kont ->
      let result =
        match sys.sys_accept listener with
        | fd, _ ->
            (try Unix.setsockopt_float fd Unix.SO_RCVTIMEO timeout
             with Unix.Unix_error _ -> ());
            let c = !next_conn in
            next_conn := Z.succ c;
            ZTbl.replace table c fd;
            Rval.Tag (Z.zero, Rval.Int c)
        | exception Unix.Unix_error ((Unix.EBADF | Unix.EINVAL), _, _) ->
            (* the wrapper closed the listener: the input is DONE — the
               reference's script-exhausted VALUE *)
            tag_exhausted
        | exception Unix.Unix_error (e, _, _) ->
            env_fail ("accept: " ^ Unix.error_message e)
      in
      Effect.Deep.continue kont result
  | effect Recv (cv, nv), kont ->
      let c = match cv with Rval.Int z -> z | _ -> raise Rval.Stuck in
      let maxlen = match nv with Rval.Int z -> z | _ -> raise Rval.Stuck in
      if Z.leq maxlen Z.zero then raise Rval.Stuck;
      let result =
        match ZTbl.find_opt table c with
        | Some fd -> Rval.Bytes (recv_full sys fd (Z.to_int maxlen))
        | None -> tag_ebadf
      in
      Effect.Deep.continue kont result
  | effect Send (cv, bv), kont ->
      let c = match cv with Rval.Int z -> z | _ -> raise Rval.Stuck in
      let b = match bv with Rval.Bytes b -> b | _ -> raise Rval.Stuck in
      let result =
        match ZTbl.find_opt table c with
        | Some fd -> send_full sys fd b; Rval.Unit
        | None -> tag_ebadf
      in
      Effect.Deep.continue kont result
  | effect CloseConn cv, kont ->
      let c = match cv with Rval.Int z -> z | _ -> raise Rval.Stuck in
      let result =
        match ZTbl.find_opt table c with
        | Some fd ->
            (match sys.sys_close fd with
             | () -> ()
             | exception Unix.Unix_error (e, _, _) ->
                 env_fail ("close: " ^ Unix.error_message e));
            ZTbl.remove table c;
            Rval.Bool true
        | None -> Rval.Bool false
      in
      Effect.Deep.continue kont result

let run_checked ?(sys = real_sys) ?(timeout = 5.0) ~listener f =
  try Ok (run ~sys ~timeout ~listener f) with
  | Env_failure v -> Error (`Environmental v)
  | Effect.Unhandled _ as e -> Error (`Unhandled_effect (Printexc.to_string e))
  | e -> Error (`Unexpected_exception (Printexc.to_string e))
