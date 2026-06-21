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

(* Reverse direction: build the extracted Coq integers from zarith, so the differential
   test can construct adversarial reference states (kb/plan.md Resolution 5). *)
let rec pos_of_z (z : Z.t) : BinNums.positive =
  (* [positive] encodes strictly-positive integers; guard the precondition instead of
     looping forever on 0 / negatives (audit M5). Callers go through [coqz_of_z]. *)
  if Z.sign z <= 0 then invalid_arg "Coqconv.pos_of_z: argument must be >= 1";
  if Z.equal z Z.one then BinNums.Coq_xH
  else if Z.equal (Z.rem z (Z.of_int 2)) Z.zero then
    BinNums.Coq_xO (pos_of_z (Z.div z (Z.of_int 2)))
  else BinNums.Coq_xI (pos_of_z (Z.div z (Z.of_int 2)))

let coqz_of_z (z : Z.t) : BinNums.coq_Z =
  match Z.sign z with
  | 0 -> BinNums.Z0
  | s when s > 0 -> BinNums.Zpos (pos_of_z z)
  | _ -> BinNums.Zneg (pos_of_z (Z.neg z))

let rec int_of_nat (n : Datatypes.nat) : int =
  match n with Datatypes.O -> 0 | Datatypes.S m -> 1 + int_of_nat m

let rec list_of_coq (l : 'a Datatypes.list) : 'a list =
  match l with
  | Datatypes.Coq_nil -> []
  | Datatypes.Coq_cons (x, tl) -> x :: list_of_coq tl
