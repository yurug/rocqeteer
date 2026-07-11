(** Runtime Time realizer: the OCaml backend for the [ONow] effect (R5, adr-0011).

    The handler's clock SOURCE is injectable (`unit -> Z.t`, milliseconds): production
    uses the wall clock; tests inject a harness-controlled virtual clock that is stepped
    only BETWEEN runs, so reference and fast sides see one instant per run (the
    determinism protocol of adr-0011 §Decision 4). The store realizer (runtime/kv.ml)
    must read the SAME source instance — construct both through
    [Runtime.with_store_and_time], the single composition point; that single-source
    discipline is the named manifest assumption [Runtime_SingleTimeSource_refines].

    [now] returns [Rval.Int] (the reference ONow returns [DInt now_ms]).

    Dependency note: the production wall clock needs [Unix.gettimeofday] — the OCaml
    stdlib has no wall clock ([Sys.time] is CPU time). `unix` ships with the OCaml
    compiler distribution (not a new opam dependency), added to runtime/dune for this
    one symbol and recorded in docs/runtime_manifest.toml (effect."Time"). *)

type source = unit -> Z.t

type _ Effect.t += Now : Z.t Effect.t

(** The curried public wrapper — what generated code calls for [ONow]. *)
let now () : Rval.t = Rval.Int (Effect.perform Now)

(** Deep handler: each [Now] resumes with a fresh read of [src]. With the test protocol
    (source stepped only between runs) every read within a run yields the same instant,
    matching the reference's immutable [world.now_ms]. *)
let run (src : source) (f : unit -> 'a) : 'a =
  match f () with
  | v -> v
  | effect Now, k -> Effect.Deep.continue k (src ())

(** Production default: wall clock in milliseconds (truncated toward zero). *)
let wall_clock_ms : source = fun () -> Z.of_float (Unix.gettimeofday () *. 1000.)
