(** Runtime Cache realizer: the OCaml backend for [OCacheGet]/[OCachePut] — a memo store.

    Observationally invisible: the cache is a separate [Hashtbl] the handler holds; it never
    appears in the KV observable. A program that memoizes correctly produces the same
    KV/trace result whether the cache hits or misses (kb/spec/effect-signatures.md). *)

module T = Hashtbl.Make (struct
  type t = Z.t

  let equal = Z.equal
  let hash z = Hashtbl.hash (Z.to_string z)
end)

type _ Effect.t += CGet : Z.t -> Z.t option Effect.t | CPut : (Z.t * Z.t) -> unit Effect.t

let get k = Effect.perform (CGet k)
let put k v = Effect.perform (CPut (k, v))

let run (tbl : Z.t T.t) (f : unit -> 'a) : 'a =
  match f () with
  | v -> v
  | effect CGet k, kont -> Effect.Deep.continue kont (T.find_opt tbl k)
  | effect CPut (k, v), kont ->
      T.replace tbl k v;
      Effect.Deep.continue kont ()
