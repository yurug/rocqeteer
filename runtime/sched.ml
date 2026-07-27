(** Runtime cooperative scheduler: the OCaml 5 backend for the C5 concurrency ops
    (adr-0019), the executable counterpart of [theories/Sched.v].

    The five ops become effects; a deep handler PARKS each one-shot continuation and
    hands control back to a scheduler LOOP driven by an INJECTED schedule (the reference
    [Sched.run_sched]'s oracle — determinism by injection, not by a free runtime
    choice).  This is the near-idiomatic Eio-style fiber structure WITHOUT the Eio
    dependency (adr-0003 budget unchanged: stdlib [Effect] only).

    One-shot discipline (invariant 7): every captured continuation is resumed AT MOST
    ONCE (via [Effect.Deep.continue]); never multi-shot.  A continuation parked at
    schedule's end is simply dropped.

    Correspondence with [Sched.sched_one] (one schedule slot = advance one fiber from
    one scheduling point to the next, then act on the op it lands on and re-park):
      - Yield      -> re-park, deliver [Unit] next slot
      - ChanMake   -> allocate next channel id, deliver [Int c]
      - ChanSend   -> enqueue on the channel (no-op if absent), deliver [Unit]
      - ChanRecv   -> dequeue if non-empty (deliver value); EMPTY blocks — the slot is
                      consumed with NO progress, the fiber re-checks when next scheduled
      - Spawn i    -> allocate next fiber id, add [bodies i], deliver the new [Int id]
    Channels are the ONLY sharing (no shared memory — no data race representable).  A
    schedule that ends with fibers still live is [Stuck] (deadlock is a value, never a
    hang), mirroring [Sched.sresult_of]. *)

type _ Effect.t +=
  | Spawn    : Z.t -> Rval.t Effect.t          (* body index -> new fiber id (Int) *)
  | Yield    : Rval.t Effect.t                 (* -> Unit *)
  | ChanMake : Rval.t Effect.t                 (* -> new channel id (Int) *)
  | ChanSend : (Z.t * Rval.t) -> Rval.t Effect.t   (* (chan, value) -> Unit *)
  | ChanRecv : Z.t -> Rval.t Effect.t          (* chan -> value *)

let spawn (body_index : Z.t) : Rval.t = Effect.perform (Spawn body_index)
let yield () : Rval.t = Effect.perform Yield
let chan_make () : Rval.t = Effect.perform ChanMake
let chan_send (c : Z.t) (v : Rval.t) : Rval.t = Effect.perform (ChanSend (c, v))
let chan_recv (c : Z.t) : Rval.t = Effect.perform (ChanRecv c)

(** Completed fibers in completion order, or (on deadlock/short schedule) the ids of
    the fibers still live plus what completed — mirrors [Sched.sresult]. *)
type result =
  | Completed of (Z.t * Rval.t) list
  | Stuck     of Z.t list * (Z.t * Rval.t) list

let string_of_result = function
  | Completed d ->
      "Completed ["
      ^ String.concat "; "
          (List.map (fun (i, v) -> Z.to_string i ^ "->" ^ Rval.to_string v) d)
      ^ "]"
  | Stuck (r, d) ->
      "Stuck (live=[" ^ String.concat "; " (List.map Z.to_string r) ^ "], done=["
      ^ String.concat "; "
          (List.map (fun (i, v) -> Z.to_string i ^ "->" ^ Rval.to_string v) d)
      ^ "])"

(** What a fiber does when it reaches its next scheduling point (or returns).  Each
    carries the one-shot resume that drives it to the FOLLOWING scheduling point. *)
type req =
  | Done     of Rval.t
  | Yielded  of (Rval.t -> req)
  | ChanMade of (Rval.t -> req)
  | Sent     of Z.t * Rval.t * (Rval.t -> req)
  | Received of Z.t * (Rval.t -> req)
  | Spawned  of Z.t * (Rval.t -> req)

let handler : (Rval.t, req) Effect.Deep.handler =
  { retc = (fun v -> Done v)
  ; exnc = (fun e -> raise e)
  ; effc =
      (fun (type a) (eff : a Effect.t) ->
        (* Each arm refines [a = Rval.t] (the effects are GADTs), so the parked
           resume [fun r -> continue k r] is well typed.  The resume is a one-shot:
           [continue] fires the captured continuation at most once. *)
        match eff with
        | Yield ->
            Some (fun (k : (a, req) Effect.Deep.continuation) ->
                Yielded (fun r -> Effect.Deep.continue k r))
        | ChanMake ->
            Some (fun (k : (a, req) Effect.Deep.continuation) ->
                ChanMade (fun r -> Effect.Deep.continue k r))
        | ChanSend (c, v) ->
            Some (fun (k : (a, req) Effect.Deep.continuation) ->
                Sent (c, v, fun r -> Effect.Deep.continue k r))
        | ChanRecv c ->
            Some (fun (k : (a, req) Effect.Deep.continuation) ->
                Received (c, fun r -> Effect.Deep.continue k r))
        | Spawn b ->
            Some (fun (k : (a, req) Effect.Deep.continuation) ->
                Spawned (b, fun r -> Effect.Deep.continue k r))
        | _ -> None)
  }

module ZTbl = Hashtbl.Make (struct
  type t = Z.t
  let equal = Z.equal
  let hash z = Hashtbl.hash (Z.to_string z)
end)

(** Run [init] fibers under [schedule], with spawn bodies [bodies] and pre-made
    channels [chans].  [next_fib]/[next_chan] seed the id counters (the reference's
    [snextf]/[snextc]).  Trace and any leaf effects (store/socket) must be handled by
    ENCLOSING handlers — this scheduler only intercepts the five concurrency ops. *)
let run ?(next_fib = Z.of_int 3) ?(next_chan = Z.one) ?(chans = [])
    ~(bodies : Z.t -> unit -> Rval.t) ~(schedule : Z.t list)
    (init : (Z.t * (unit -> Rval.t)) list) : result =
  let fibers : (unit -> req) ZTbl.t = ZTbl.create 8 in
  let chan_q : Rval.t Queue.t ZTbl.t = ZTbl.create 8 in
  let order = ref [] in                 (* every id ever added, in order *)
  let done_list = ref [] in             (* reversed; completion order *)
  let next_fib = ref next_fib in
  let next_chan = ref next_chan in
  List.iter (fun c -> ZTbl.replace chan_q c (Queue.create ())) chans;
  let add id thunk = ZTbl.replace fibers id thunk; order := !order @ [ id ] in
  List.iter
    (fun (id, body) -> add id (fun () -> Effect.Deep.match_with body () handler))
    init;
  let park id res r = ZTbl.replace fibers id (fun () -> res r) in
  let step fid =
    match ZTbl.find_opt fibers fid with
    | None -> ()                        (* absent / already completed: no-op *)
    | Some thunk ->
        (match thunk () with
         | Done v ->
             ZTbl.remove fibers fid;
             done_list := (fid, v) :: !done_list
         | Yielded res -> park fid res Rval.Unit
         | ChanMade res ->
             let c = !next_chan in
             next_chan := Z.succ c;
             ZTbl.replace chan_q c (Queue.create ());
             park fid res (Rval.Int c)
         | Sent (c, v, res) ->
             (match ZTbl.find_opt chan_q c with
              | Some q -> Queue.add v q
              | None -> ());            (* enqueue on a missing chan is a no-op *)
             park fid res Rval.Unit
         | Received (c, res) ->
             (* If data waits, DELIVER it (park the resume) — the continuation runs on
                the fiber's NEXT slot, exactly as the reference parks [FR (ORet v) k]
                and defers [k] to the next [sched_one].  Otherwise BLOCK: re-park to
                re-check the channel next slot, no progress. *)
             (match ZTbl.find_opt chan_q c with
              | Some q when not (Queue.is_empty q) -> park fid res (Queue.pop q)
              | _ -> ZTbl.replace fibers fid (fun () -> Received (c, res)))
         | Spawned (b, res) ->
             let nf = !next_fib in
             next_fib := Z.succ nf;
             add nf (fun () -> Effect.Deep.match_with (bodies b) () handler);
             park fid res (Rval.Int nf))
  in
  List.iter step schedule;
  let live = List.filter (ZTbl.mem fibers) !order in
  match live with
  | [] -> Completed (List.rev !done_list)
  | _ -> Stuck (live, List.rev !done_list)
