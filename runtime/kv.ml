(** Runtime store effect, deep handler, and observable normalizer (R4, adr-0011).

    The OCaml side of the trust boundary: a native effect + a [Hashtbl] handler that the
    generated direct-style code performs against.  Keys are native [bytes] (the reference
    converts [list ascii] to string keys at the op boundary); each binding holds
    [(Rval.t * Z.t option)] — the value plus an optional absolute deadline in ms.

    LIVENESS (the ONE rule, adr-0011 §Decision 3): a binding [(v, Some d)] is live iff
    [now <= d] — alive AT the deadline, dead strictly after; [(v, None)] is always live.
    Expired bindings are semantically ABSENT for every op and for [observe]; whether they
    are physically deleted is unobservable freedom (this handler deletes them LAZILY, on
    the read that discovers the expiry).

    [now] comes from a [Time.source] closure — the SAME instance that drives the Time
    handler, via [Runtime.with_store_and_time] (assumption
    Runtime_SingleTimeSource_refines in docs/runtime_manifest.toml).

    All op results are [Rval.t], mirroring the reference dvals:
      get: DNone | DSome v · put: DUnit (clears deadline) · delete: DBool live-removal ·
      get_deadline: DNone | DSome DNone | DSome (DSome (DInt d)) ·
      set_deadline (None | Some (Int d)): DBool live-modified. *)

type key = bytes
type value = Rval.t

(** A stored binding: the value plus an optional absolute deadline (ms). *)
type entry = Rval.t * Z.t option

(** Bytes-keyed table; [observe] sorts it, so iteration order is not observable (T7). *)
module T = Hashtbl.Make (struct
  type t = bytes

  let equal = Bytes.equal
  let hash b = Hashtbl.hash (Bytes.to_string b)
end)

(** [live now e]: the boundary rule, verbatim from the reference [live] in EffIR.v. *)
let live (now : Z.t) ((_, dl) : entry) : bool =
  match dl with
  | None -> true
  | Some d -> Z.leq now d

(* Tupled constructors (Resolution 7); kept here, never performed outside this module.
   The effect types carry [Rval.t] results so the return value is already in the dval
   universe, matching the reference semantics. [SetDeadline]'s second component is the
   OSetDeadline argument val (Rval.None | Rval.Some (Rval.Int d)). *)
type _ Effect.t +=
  | Get : key -> value Effect.t
  | Put : (key * value) -> value Effect.t
  | Delete : key -> value Effect.t
  | GetDeadline : key -> value Effect.t
  | SetDeadline : (key * value) -> value Effect.t

(* Curried public wrappers — what generated code calls. *)
let get k = Effect.perform (Get k)
let put k v = Effect.perform (Put (k, v))
let delete k = Effect.perform (Delete k)
let get_deadline k = Effect.perform (GetDeadline k)
let set_deadline k d = Effect.perform (SetDeadline (k, d))

(** Deep handler. [now] is the shared time source (read per op; the test protocol steps
    the source only between runs, so a run sees one instant — adr-0011 §Decision 4).
    Each continuation is resumed exactly once (one-shot; kb/external/ocaml5-effects.md). *)
let run ~(now : Time.source) (table : entry T.t) (f : unit -> 'a) : 'a =
  (* The LIVE view of a key; an expired binding found here is physically removed
     (lazy deletion — unobservable implementation freedom). *)
  let find_live k : entry option =
    match T.find_opt table k with
    | Some e when live (now ()) e -> Some e
    | Some _ ->
        T.remove table k;
        None
    | None -> None
  in
  match f () with
  | v -> v
  | effect Get k, kont ->
      Effect.Deep.continue kont
        (match find_live k with
         | Some (v, _) -> Rval.Some v
         | None -> Rval.None)
  | effect Put (k, v), kont ->
      (* stores the value and CLEARS any deadline (adr-0011 op table) *)
      T.replace table k (v, None);
      Effect.Deep.continue kont Rval.Unit
  | effect Delete k, kont ->
      let was_live = match find_live k with Some _ -> true | None -> false in
      T.remove table k;
      Effect.Deep.continue kont (Rval.Bool was_live)
  | effect GetDeadline k, kont ->
      Effect.Deep.continue kont
        (match find_live k with
         | Some (_, None) -> Rval.Some Rval.None
         | Some (_, Some d) -> Rval.Some (Rval.Some (Rval.Int d))
         | None -> Rval.None)
  | effect SetDeadline (k, dv), kont ->
      let dl =
        match dv with
        | Rval.None -> None
        | Rval.Some (Rval.Int d) -> Some d
        | _ -> raise Rval.Stuck (* malformed arg — mirrors the reference Dstuck *)
      in
      (match find_live k with
       | Some (v, _) ->
           T.replace table k (v, dl);
           Effect.Deep.continue kont (Rval.Bool true)
       | None -> Effect.Deep.continue kont (Rval.Bool false))

(** A failure surfaced at a public boundary, as a typed value (kb/spec/error-taxonomy.md §2). *)
type error =
  [ `Unhandled_effect of string
  | `Unexpected_exception of string ]

let string_of_error = function
  | `Unhandled_effect s -> "unhandled effect: " ^ s
  | `Unexpected_exception s -> "unexpected exception: " ^ s

(** Checked entrypoint: an unhandled effect OR any stray exception becomes a typed error,
    never a crash (edge case T8 / audit C1). The boundary is the only place failures
    become observable, and there they are always typed (kb/conventions/error-handling.md). *)
let run_checked ~now table f =
  try Ok (run ~now table f) with
  | Effect.Unhandled _ as e -> Error (`Unhandled_effect (Printexc.to_string e))
  | e -> Error (`Unexpected_exception (Printexc.to_string e))

(** Order-independent observable for differential testing: sorted (key, entry), LIVE
    bindings only — expired bindings are filtered exactly as the reference
    [live_elements] does. *)
let observe ~(now : Z.t) (table : entry T.t) : (bytes * entry) list =
  T.fold (fun k e acc -> if live now e then (k, e) :: acc else acc) table []
  |> List.sort (fun (a, _) (b, _) -> Bytes.compare a b)
