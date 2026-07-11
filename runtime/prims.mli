(** OCaml realizers for the v1 primitive set (adr-0009-vprim-registry).

    All functions are total; they return [Rval.t] using [Rval.None] for [DNone] and
    [Rval.Some v] for [DSome v], matching the [opt_to_rval] convention in [kv.ml].
    No exceptions escape. The symbols listed here are the registered realizer names
    referenced in [docs/runtime_manifest.toml] and emitted by [codegen/codegen.ml]. *)

val prim_add_checked  : Rval.t -> Rval.t -> Rval.t
val prim_sub_checked  : Rval.t -> Rval.t -> Rval.t
val prim_cmp_int      : Rval.t -> Rval.t -> Rval.t
val prim_eq_bytes     : Rval.t -> Rval.t -> Rval.t
val prim_bytes_len    : Rval.t -> Rval.t
val prim_bytes_concat : Rval.t -> Rval.t -> Rval.t
val prim_bytes_sub    : Rval.t -> Rval.t -> Rval.t -> Rval.t
val prim_parse_int64  : Rval.t -> Rval.t
val prim_print_int    : Rval.t -> Rval.t
