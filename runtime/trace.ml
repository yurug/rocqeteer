(** Runtime Trace realizer: the OCaml backend for the [OTrace] effect — an append-only log.

    [OTrace v] appends [v] to a buffer the handler holds; nothing else is observable
    (kb/spec/effect-signatures.md). The buffer stores newest-first; [contents] reverses it
    to chronological order, matching the reference (which stores [trace] reversed too).
    Event type is now [Rval.t] (IR v2 milestone 1). *)

type _ Effect.t += Emit : Rval.t -> unit Effect.t

let emit (v : Rval.t) : unit = Effect.perform (Emit v)

let run (buf : Rval.t list ref) (f : unit -> 'a) : 'a =
  match f () with
  | v -> v
  | effect Emit x, k ->
      buf := x :: !buf;
      Effect.Deep.continue k ()

let contents (buf : Rval.t list ref) : Rval.t list = List.rev !buf
