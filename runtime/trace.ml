(** Runtime Trace realizer: the OCaml backend for the [OTrace] effect — an append-only log.

    [OTrace v] appends [v] to a buffer the handler holds; nothing else is observable
    (kb/spec/effect-signatures.md). The buffer stores newest-first; [contents] reverses it
    to chronological order, matching the reference (which stores [trace] reversed too). *)

type _ Effect.t += Emit : Z.t -> unit Effect.t

let emit (v : Z.t) : unit = Effect.perform (Emit v)

let run (buf : Z.t list ref) (f : unit -> 'a) : 'a =
  match f () with
  | v -> v
  | effect Emit x, k ->
      buf := x :: !buf;
      Effect.Deep.continue k ()

let contents (buf : Z.t list ref) : Z.t list = List.rev !buf
