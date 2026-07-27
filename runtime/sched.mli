(** Public interface of the cooperative scheduler realizer (C5, adr-0019) — the
    executable counterpart of [theories/Sched.v].

    Determinism by INJECTION: [run] is a function of the [schedule] (a fiber-id
    sequence), exactly as the reference [Sched.run_sched].  One-shot continuations
    only (invariant 7).  Channels are the only sharing.  Deadlock (a schedule that
    leaves fibers live) is the [Stuck] value, never a hang.

    Trace and leaf effects (store/socket) are handled by ENCLOSING handlers; this
    scheduler intercepts only the five concurrency ops. *)

type _ Effect.t +=
  | Spawn    : Z.t -> Rval.t Effect.t
  | Yield    : Rval.t Effect.t
  | ChanMake : Rval.t Effect.t
  | ChanSend : (Z.t * Rval.t) -> Rval.t Effect.t
  | ChanRecv : Z.t -> Rval.t Effect.t

val spawn : Z.t -> Rval.t
val yield : unit -> Rval.t
val chan_make : unit -> Rval.t
val chan_send : Z.t -> Rval.t -> Rval.t
val chan_recv : Z.t -> Rval.t

type result =
  | Completed of (Z.t * Rval.t) list
  | Stuck     of Z.t list * (Z.t * Rval.t) list

val string_of_result : result -> string

(** [run ~bodies ~schedule init] drives the [init] fibers (id, thunk) under
    [schedule].  [bodies] resolves an [OSpawn] index to a fiber body; [chans]
    pre-creates channel ids (the driver's listener channel); [next_fib]/[next_chan]
    seed the id counters ([snextf]/[snextc]). *)
val run :
  ?next_fib:Z.t ->
  ?next_chan:Z.t ->
  ?chans:Z.t list ->
  bodies:(Z.t -> unit -> Rval.t) ->
  schedule:Z.t list ->
  (Z.t * (unit -> Rval.t)) list ->
  result
