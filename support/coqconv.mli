(** Converters between the extracted Coq ADTs and native OCaml / zarith (kb/plan.md R4/R5). *)

val z_of_coqz : Ref_extracted.BinNums.coq_Z -> Z.t
val coqz_of_z : Z.t -> Ref_extracted.BinNums.coq_Z
val bool_of_coq : Ref_extracted.Datatypes.bool -> bool
val int_of_nat : Ref_extracted.Datatypes.nat -> int
val list_of_coq : 'a Ref_extracted.Datatypes.list -> 'a list
val string_of_coq : Ref_extracted.String.string -> string
val char_of_ascii : Ref_extracted.Ascii.ascii -> char

(** Convert a Coq [list ascii] (extracted [DBytes] payload) to native [bytes]. *)
val ascii_list_to_bytes : Ref_extracted.Ascii.ascii Ref_extracted.Datatypes.list -> bytes

(** Convert native [bytes] back to a Coq [list ascii] (for [dval_of_rval]). *)
val bytes_to_ascii_list : bytes -> Ref_extracted.Ascii.ascii Ref_extracted.Datatypes.list

(** Convert an extracted [dval] to the native [Rkv.Rval.t].  Total for all current
    constructors; [Dstuck] raises [Rkv.Rval.Stuck] since it is never produced for
    well-typed closed terms and has no runtime representation. *)
val rval_of_dval : Ref_extracted.EffIR.dval -> Rkv.Rval.t

(** Convert a native [Rkv.Rval.t] back to an extracted [dval].  Total for all
    current constructors. *)
val dval_of_rval : Rkv.Rval.t -> Ref_extracted.EffIR.dval
