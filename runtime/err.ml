(** Runtime Error realizer: the OCaml backend for the [OThrow] effect.

    [OThrow e] is realized as a native exception (the exception backend of kb/spec/
    error-taxonomy.md / kb/conventions/error-handling.md); [run_error] is the checked
    runner that turns it into a typed [result], so a throw aborts the computation exactly
    like the reference [OErr] short-circuit, committing whatever state preceded it. *)

exception Runtime_error of Z.t

(** Abort with error value [e] (slice-1 error values are Z, like KV values). *)
let throw (e : Z.t) : 'a = raise (Runtime_error e)

(** Run [f], converting a thrown error into [Error e]; other exceptions propagate. *)
let run_error (f : unit -> 'a) : ('a, Z.t) result =
  try Ok (f ()) with Runtime_error e -> Error e
