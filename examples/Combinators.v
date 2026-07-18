(** * Gallery — the computational glue: [Match], [Repeat], [Fold], prims

    Not effects, but what real effectful programs are made of:
    - [Match]: depth-1 patterns over structured values (tags bind payloads);
    - [Repeat n body]: the bounded loop (fuel is structural, totality is free);
    - [Fold lst init body]: list elimination with an accumulator — argv
      processing, reply building;
    - [Prim]: 16 total checked primitives (overflow -> [DNone], never garbage).

    Deep dive: theories/Recur.v (Repeat by induction), theories/Fold.v
    (invariant rules), theories/Prims.v, theories/StructVal.v. *)
From Stdlib Require Import ZArith List Ascii String.
From Rocqeteer Require Import EffIR.
Import ListNotations.
Local Open Scope Z_scope.

Definition k : list ascii := list_ascii_of_string "n".

(** Repeat: increment a key five times (read-modify-write in the body;
    theories/Recur.v proves the general "after n iterations, value = n"). *)
Definition incr_k : tm :=
  Bind (Perform OGet [VBytes k])
       (Match (VVar 0)
         [(PSome, Bind (Prim PAddChecked [VVar 0; VInt 1])
                       (Match (VVar 0)
                         [(PSome, Perform OPut [VBytes k; VVar 0])]
                         (Perform OThrow [VBytes (list_ascii_of_string "overflow")])))]
         (Perform OPut [VBytes k; VInt 1])).

Theorem five_increments :
  let '(o, _) := run_top DUnit 0
    (Bind (Repeat 5 incr_k) (Perform OGet [VBytes k])) in
  o = ORet (DSome (DInt 5)).
Proof. vm_compute. reflexivity. Qed.

(** Fold: sum a list of ints with the CHECKED adder — the accumulator is
    de Bruijn 0 in the body, the element is 1; overflow aborts the fold. *)
Definition sum_list : tm :=
  Fold (VVar 0) (Ret (VInt 0))
       (Bind (Prim PAddChecked [VVar 1; VVar 0])
             (Match (VVar 0)
               [(PSome, Ret (VVar 0))]
               (Perform OThrow [VBytes (list_ascii_of_string "sum overflow")]))).

Theorem sums_the_context :
  let '(o, _) := run_top (DList [DInt 10; DInt 20; DInt 12]) 0
                   (Bind (Perform OAsk []) sum_list) in
  o = ORet (DInt 42).
Proof. vm_compute. reflexivity. Qed.

(** Match on tagged unions: DTag is the sum injection; PTag binds the payload. *)
Theorem tag_dispatch :
  let '(o, _) := run_top (DTag 1 (DInt 5)) 0
    (Bind (Perform OAsk [])
          (Match (VVar 0)
            [(PTag 0, Ret (VBytes (list_ascii_of_string "left")));
             (PTag 1, Ret (VVar 0))]
            (Perform OThrow [VBytes (list_ascii_of_string "bad tag")]))) in
  o = ORet (DInt 5).
Proof. vm_compute. reflexivity. Qed.

(** Checked prims fail SOFT: parse of malformed bytes is DNone, not chaos. *)
Theorem parse_is_checked :
  let '(o, _) := run_top DUnit 0
    (Prim PParseInt64 [VBytes (list_ascii_of_string "12x4")]) in
  o = ORet DNone.
Proof. vm_compute. reflexivity. Qed.
