(** Converters between the extracted Coq ADTs and native OCaml / zarith (kb/plan.md R4/R5). *)

val z_of_coqz : Ref_extracted.BinNums.coq_Z -> Z.t
val coqz_of_z : Z.t -> Ref_extracted.BinNums.coq_Z
val bool_of_coq : Ref_extracted.Datatypes.bool -> bool
val int_of_nat : Ref_extracted.Datatypes.nat -> int
val list_of_coq : 'a Ref_extracted.Datatypes.list -> 'a list

(** Reverse direction: build a Coq [list] from a native OCaml list (R7, used by
    [dval_of_rval]'s [DList] case and by tests constructing extracted values directly). *)
val coq_list_of : 'a list -> 'a Ref_extracted.Datatypes.list
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

(** R4 (adr-0011) store-key bridge: native [bytes] <-> Coq [String.string] (the
    reference store map key, built from list-ascii payloads at the op boundary). *)
val coq_string_of_bytes : bytes -> Ref_extracted.String.string
val bytes_of_coq_string : Ref_extracted.String.string -> bytes

(** Deadline bridge: native [Z.t option] <-> extracted [coq_Z option]. *)
val coq_deadline_of : Z.t option -> Ref_extracted.BinNums.coq_Z Ref_extracted.Datatypes.option
val deadline_of_coq : Ref_extracted.BinNums.coq_Z Ref_extracted.Datatypes.option -> Z.t option

(** Store-entry bridge (R4): a native runtime entry [(Rval.t * Z.t option)] <-> the
    extracted reference [entry] = (dval, coq_Z option) prod. *)
val coq_entry_of_rval :
  Rkv.Rval.t * Z.t option ->
  (Ref_extracted.EffIR.dval, Ref_extracted.BinNums.coq_Z Ref_extracted.Datatypes.option)
    Ref_extracted.Datatypes.prod
val rval_entry_of_coq :
  (Ref_extracted.EffIR.dval, Ref_extracted.BinNums.coq_Z Ref_extracted.Datatypes.option)
    Ref_extracted.Datatypes.prod ->
  Rkv.Rval.t * Z.t option
