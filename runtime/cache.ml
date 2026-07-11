(** Runtime Cache realizer: the OCaml backend for [OCacheGet]/[OCachePut] — a memo store.

    Observationally invisible: the cache is a separate [Hashtbl] the handler holds; it never
    appears in the KV observable. A program that memoizes correctly produces the same
    KV/trace result whether the cache hits or misses (kb/spec/effect-signatures.md).
    Cache values are [Rval.t]; keys are native [bytes] since R4 (adr-0011 — one key
    discipline across the value-keyed effects). The cache has NO deadlines.

    [CGet] returns [Rval.t] (not [Rval.t option]): absent keys become [Rval.None] and
    present keys become [Rval.Some v], matching [opt_to_dval] in the reference semantics. *)

module T = Hashtbl.Make (struct
  type t = bytes

  let equal = Bytes.equal
  let hash b = Hashtbl.hash (Bytes.to_string b)
end)

let opt_to_rval : Rval.t option -> Rval.t = function
  | None   -> Rval.None
  | Some v -> Rval.Some v

type _ Effect.t +=
  | CGet : bytes -> Rval.t Effect.t
  | CPut : (bytes * Rval.t) -> unit Effect.t

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
