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
val prim_mul_checked  : Rval.t -> Rval.t -> Rval.t
val prim_list_len     : Rval.t -> Rval.t
val prim_list_nth     : Rval.t -> Rval.t -> Rval.t

(** FLOOR division (Z.fdiv — the Rocq reference's Z.div is floor, zarith's Z.div is
    truncation); [Rval.None] on divisor 0 or shape mismatch — no exception (R9). *)
val prim_div_floor    : Rval.t -> Rval.t -> Rval.t

(** ASCII case folding (R12): 65-90 shifted +32 (lower) resp. 97-122 shifted -32
    (upper); every other byte unchanged, incl. > 127 — no locale, no UTF-8. Fresh
    output buffer (the input is never mutated); [Rval.None] on shape mismatch. *)
val prim_lower_bytes  : Rval.t -> Rval.t
val prim_upper_bytes  : Rval.t -> Rval.t

(** List snoc (R13): [List vs, v] -> [List (vs @ [v])] — appends [v] (ANY value,
    incl. nested List/Tag) at the END; order-preserving; non-List first arg ->
    [Rval.None]. O(n) per snoc (documented in prims.ml: collecting folds are
    O(n^2) worst-case, bounded by the consumer's multibulk cap; a deque realizer
    is premature). Fresh spine — the input list is never mutated. *)
val prim_list_snoc    : Rval.t -> Rval.t -> Rval.t
val prim_find_sub     : Rval.t -> Rval.t -> Rval.t
