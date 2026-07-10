(** Runtime Cache realizer: the OCaml backend for [OCacheGet]/[OCachePut] — a memo store.

    Observationally invisible: the cache is a separate [Hashtbl] the handler holds; it never
    appears in the KV observable. A program that memoizes correctly produces the same
    KV/trace result whether the cache hits or misses (kb/spec/effect-signatures.md).
    Cache values are now [Rval.t] (IR v2 milestone 1).

    [CGet] returns [Rval.t] (not [Rval.t option]): absent keys become [Rval.None] and
    present keys become [Rval.Some v], matching [opt_to_dval] in the reference semantics. *)

module T = Hashtbl.Make (struct
  type t = Z.t

  let equal = Z.equal
  let hash z = Hashtbl.hash (Z.to_string z)
end)

let opt_to_rval : Rval.t option -> Rval.t = function
  | None   -> Rval.None
  | Some v -> Rval.Some v

type _ Effect.t +=
  | CGet : Z.t -> Rval.t Effect.t
  | CPut : (Z.t * Rval.t) -> unit Effect.t

let get k = Effect.perform (CGet k)
let put k v = Effect.perform (CPut (k, v))

let run (tbl : Rval.t T.t) (f : unit -> 'a) : 'a =
  match f () with
  | v -> v
  | effect CGet k, kont ->
      Effect.Deep.continue kont (opt_to_rval (T.find_opt tbl k))
  | effect CPut (k, v), kont ->
      T.replace tbl k v;
      Effect.Deep.continue kont ()
