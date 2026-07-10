(** Runtime Env realizer: the OCaml backend for the [OAsk] effect — a read-only context.

    [OAsk] reads an ambient value supplied by [run]; the handler resumes with it and never
    mutates anything (kb/spec/effect-signatures.md).  Context type is now [Rval.t] to match
    the dval universe in theories/EffIR.v (IR v2 milestone 1). *)

type ctx = Rval.t

type _ Effect.t += Ask : ctx Effect.t

let ask () : ctx = Effect.perform Ask

(** Install the read-only context [c] around [f]; each Ask resumes with [c]. *)
let run (c : ctx) (f : unit -> 'a) : 'a =
  match f () with
  | v -> v
  | effect Ask, k -> Effect.Deep.continue k c
