(** Public interface of the runtime store realizer (R4, adr-0011).

    The effect CONSTRUCTORS are deliberately NOT exported: clients (and generated code)
    call the curried wrappers, never [Effect.perform] directly. Hiding the constructors
    makes that a compiler-checked invariant rather than a convention
    (kb/spec/effect-signatures.md, audit C1).

    Keys are native [bytes]; each binding holds [(Rval.t * Z.t option)] — value plus
    optional absolute deadline in ms. Liveness: live iff [now <= d] (alive AT the
    deadline); [None] never expires. Expired bindings are semantically absent everywhere
    (ops and [observe]); physical deletion is lazy and unobservable.

    [now] comes from a [Time.source]; use [Runtime.with_store_and_time] so the store and
    the Time handler share ONE source instance (Runtime_SingleTimeSource_refines). *)

type key = bytes
type value = Rval.t

(** A stored binding: the value plus an optional absolute deadline (ms). *)
type entry = Rval.t * Z.t option

(** A failure surfaced at a public boundary (kb/spec/error-taxonomy.md §2). *)
type error =
  [ `Unhandled_effect of string
  | `Unexpected_exception of string ]

val string_of_error : error -> string

(** Bytes-keyed table backing the handler; [observe] makes iteration order unobservable. *)
module T : Hashtbl.S with type key = bytes

(** The boundary rule, verbatim from the reference: live iff deadline absent or now <= d. *)
val live : Z.t -> entry -> bool

(** Curried public wrappers — the only way to perform a store operation. Results mirror
    the reference dvals:
    [get]: [Rval.None] (absent/expired) or [Rval.Some v];
    [put]: [Rval.Unit], stores the value and CLEARS any deadline;
    [delete]: [Rval.Bool] — true iff a LIVE binding was removed;
    [get_deadline]: [Rval.None] | [Rval.Some Rval.None] (live, no deadline)
                    | [Rval.Some (Rval.Some (Rval.Int d))];
    [set_deadline k (Rval.None | Rval.Some (Rval.Int d))]: [Rval.Bool] — true iff a
    live binding was modified. *)
val get : key -> value
val put : key -> value -> value
val delete : key -> value
val get_deadline : key -> value
val set_deadline : key -> value -> value

(** Deep handler installing the store interpretation around [f]; [now] is the shared
    time source; each continuation resumed once. *)
val run : now:Time.source -> entry T.t -> (unit -> 'a) -> 'a

(** Checked entrypoint: unhandled effects and stray exceptions become typed errors. *)
val run_checked : now:Time.source -> entry T.t -> (unit -> 'a) -> ('a, error) result

(** Order-independent observable for differential testing: sorted (key, entry) of the
    LIVE bindings at instant [now] (expired filtered, like the reference live_elements). *)
val observe : now:Z.t -> entry T.t -> (bytes * entry) list
