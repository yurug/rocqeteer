(** Converters between the extracted Coq ADTs and native OCaml / zarith (kb/plan.md R4/R5). *)

val z_of_coqz : Ref_extracted.BinNums.coq_Z -> Z.t
val coqz_of_z : Z.t -> Ref_extracted.BinNums.coq_Z
val bool_of_coq : Ref_extracted.Datatypes.bool -> bool
val int_of_nat : Ref_extracted.Datatypes.nat -> int
val list_of_coq : 'a Ref_extracted.Datatypes.list -> 'a list
