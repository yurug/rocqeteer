(** Public interface of the runtime KV realizer.

    The effect CONSTRUCTORS [Get]/[Put]/[Delete] are deliberately NOT exported: clients
    (and generated code) call the curried wrappers, never [Effect.perform] directly. Hiding
    the constructors makes that a compiler-checked invariant rather than a convention
    (kb/spec/effect-signatures.md, audit C1). *)

type key = Z.t
type value = Z.t

(** A failure surfaced at a public boundary (kb/spec/error-taxonomy.md §2). *)
type error =
  [ `Unhandled_effect of string
  | `Unexpected_exception of string ]

val string_of_error : error -> string

(** Z-keyed table backing the handler; [observe] makes iteration order unobservable. *)
module T : Hashtbl.S with type key = Z.t

(** Curried public wrappers — the only way to perform a KV operation. *)
val get : key -> value option
val put : key -> value -> unit
val delete : key -> unit

(** Deep handler installing the KV interpretation around [f]; each continuation resumed once. *)
val run : value T.t -> (unit -> 'a) -> 'a

(** Checked entrypoint: unhandled effects and stray exceptions become typed errors. *)
val run_checked : value T.t -> (unit -> 'a) -> ('a, error) result

(** Order-independent observable for differential testing: sorted (key, value). *)
val observe : value T.t -> (Z.t * Z.t) list
