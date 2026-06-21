(** Converters from the extracted Coq ADTs to native OCaml / zarith.

    Extraction is faithful, so [coq_Z], Peano [nat], and Coq [list]/[prod] come across as
    Coq inductives (kb/plan.md Resolution 4). These helpers bridge them to [Z.t]/[int]/
    native lists at the observation boundary. Shared by the codegen (integer literals) and
    the differential normalizer (kb/plan.md Resolution 5). *)

module BinNums = Ref_extracted.BinNums
module Datatypes = Ref_extracted.Datatypes

(** [Coq_xH] = 1; [Coq_xO p] = 2p; [Coq_xI p] = 2p+1 (binary positive). *)
let rec z_of_pos (p : BinNums.positive) : Z.t =
  match p with
  | BinNums.Coq_xH -> Z.one
  | BinNums.Coq_xO p -> Z.shift_left (z_of_pos p) 1
  | BinNums.Coq_xI p -> Z.succ (Z.shift_left (z_of_pos p) 1)

let z_of_coqz (z : BinNums.coq_Z) : Z.t =
  match z with
  | BinNums.Z0 -> Z.zero
  | BinNums.Zpos p -> z_of_pos p
  | BinNums.Zneg p -> Z.neg (z_of_pos p)

let bool_of_coq (b : Datatypes.bool) : bool =
  match b with Datatypes.Coq_true -> true | Datatypes.Coq_false -> false

let rec int_of_nat (n : Datatypes.nat) : int =
  match n with Datatypes.O -> 0 | Datatypes.S m -> 1 + int_of_nat m

let rec list_of_coq (l : 'a Datatypes.list) : 'a list =
  match l with
  | Datatypes.Coq_nil -> []
  | Datatypes.Coq_cons (x, tl) -> x :: list_of_coq tl
