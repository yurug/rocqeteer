(** Runtime KV effect, deep handler, and observable normalizer (slice 1).

    The OCaml side of the trust boundary: a native effect + a [Hashtbl] handler that the
    generated direct-style code performs against.  Keys stay [Z.t]; values are now [Rval.t]
    to match the dval universe in theories/EffIR.v (IR v2 milestone 1).
    (kb/architecture/decisions/adr-0004-trust-model.md, kb/external/ocaml5-effects.md).

    [Get] returns [Rval.t] (not [Rval.t option]): absent keys yield [Rval.None] and present
    keys yield [Rval.Some v], exactly as [opt_to_dval] does in the reference semantics. *)

type key = Z.t
type value = Rval.t

(** Z-keyed table; [observe] sorts it, so iteration order is not observable (T7). *)
module T = Hashtbl.Make (struct
  type t = Z.t

  let equal = Z.equal
  let hash z = Hashtbl.hash (Z.to_string z)
end)

(* Wrap an OCaml option as Rval.None / Rval.Some, matching opt_to_dval in the reference. *)
let opt_to_rval : value option -> value = function
  | None   -> Rval.None
  | Some v -> Rval.Some v

(* Tupled constructors (Resolution 7); kept here, never performed outside this module.
   The effect type carries [Rval.t] (not [Rval.t option]) so that the return value is
   already wrapped, matching the reference semantics. *)
type _ Effect.t +=
  | Get : key -> value Effect.t
  | Put : (key * value) -> unit Effect.t
  | Delete : key -> unit Effect.t

(* Curried public wrappers — what generated code calls. *)
let get k = Effect.perform (Get k)
let put k v = Effect.perform (Put (k, v))
let delete k = Effect.perform (Delete k)

(** Deep handler. The table type is annotated so its value type is concrete — otherwise
    OCaml's weak type variable would escape the per-branch effect scope. Each continuation
    is resumed exactly once (one-shot; kb/external/ocaml5-effects.md). *)
let run (table : value T.t) (f : unit -> 'a) : 'a =
  match f () with
  | v -> v
  | effect Get k, kont ->
      Effect.Deep.continue kont (opt_to_rval (T.find_opt table k))
  | effect Put (k, v), kont ->
      T.replace table k v;
      Effect.Deep.continue kont ()
  | effect Delete k, kont ->
      T.remove table k;
      Effect.Deep.continue kont ()

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
let run_checked table f =
  try Ok (run table f) with
  | Effect.Unhandled _ as e -> Error (`Unhandled_effect (Printexc.to_string e))
  | e -> Error (`Unexpected_exception (Printexc.to_string e))

(** Order-independent observable for differential testing: sorted (key, value). *)
let observe (table : value T.t) : (Z.t * Rval.t) list =
  T.fold (fun k v acc -> (k, v) :: acc) table []
  |> List.sort (fun (a, _) (b, _) -> Z.compare a b)
