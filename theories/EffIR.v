(** * EffIR — first-order effect IR (slice-1 subset) and its KV reference semantics.

    This is the SINGLE representation that the reference interpreter (here) evaluates
    and that the codegen lowers (after extraction to an OCaml ADT). Keeping one
    extrinsically-typed, first-order datatype is what guarantees "the program proved =
    the program run" — see kb/architecture/decisions/adr-0001-first-order-ast.md and
    kb/spec/effir.md.

    Slice-1 scope (kb/plan.md): the effect is KV (Get/Put/Delete); values are concrete
    Z; the only "prims" are zero/succ; the only match form is on [option] (MatchOpt).
    General prims, recursion, and other effects are deferred (kb/spec/effir.md "out of
    scope"). *)

From Stdlib Require Import ZArith List FMapAVL OrderedTypeEx.
Import ListNotations.
Local Open Scope Z_scope.

(** A Z-keyed finite map is the reference KV state. FMapAVL gives sorted [elements],
    which is exactly the order-independent observable the differential test compares
    against the OCaml Hashtbl (kb/spec/reference-semantics.md). *)
Module M := FMapAVL.Make(Z_as_OT).

(** ** Runtime values (dynamically typed).
    The interpreter is total; [Dstuck] marks an impossible/ill-typed case that proofs
    discharge as unreachable for well-typed closed terms (kb/plan.md Resolution 2). *)
Inductive dval : Type :=
| DUnit  : dval
| DBool  : bool -> dval
| DInt   : Z -> dval
| DNone  : dval
| DSome  : dval -> dval
| DPair  : dval -> dval -> dval
| Dstuck : dval.

(** ** Pure first-order expressions. [VVar] is a de Bruijn index.
    [VZero]/[VSucc] are the slice-1 pure prims (realized to Z.zero / Z.succ). *)
Inductive val : Type :=
| VVar  : nat -> val
| VUnit : val
| VBool : bool -> val
| VInt  : Z -> val
| VNone : val
| VSome : val -> val
| VPair : val -> val -> val
| VZero : val
| VSucc : val -> val.

(** ** Effect operations of the KV signature (kb/spec/effect-signatures.md). *)
Inductive op : Type := OGet | OPut | ODelete.

(** ** Effectful computations. [Bind t1 t2] binds the result of [t1] at de Bruijn 0 in
    [t2]; [MatchOpt] is the slice-1 match form (scrutinee is an [option]; the [some]
    branch binds the payload at de Bruijn 0). *)
Inductive tm : Type :=
| Ret      : val -> tm
| Bind     : tm -> tm -> tm
| Perform  : op -> list val -> tm
| MatchOpt : val -> tm -> tm -> tm.

(** ** Pure-value evaluation in a de Bruijn environment. Total: out-of-scope vars and
    type errors yield [Dstuck]. *)
Fixpoint eval_val (env : list dval) (v : val) : dval :=
  match v with
  | VVar n   => nth n env Dstuck
  | VUnit    => DUnit
  | VBool b  => DBool b
  | VInt z   => DInt z
  | VNone    => DNone
  | VSome a  => DSome (eval_val env a)
  | VPair a b => DPair (eval_val env a) (eval_val env b)
  | VZero    => DInt 0
  | VSucc a  => match eval_val env a with
                | DInt z => DInt (Z.succ z)
                | _      => Dstuck
                end
  end.

Definition state : Type := M.t dval.

Definition opt_to_dval (o : option dval) : dval :=
  match o with Some v => DSome v | None => DNone end.

(** ** Pure KV handler: the reference semantics of each operation. *)
Definition handle (o : op) (args : list dval) (s : state) : dval * state :=
  match o, args with
  | OGet,    [DInt k]        => (opt_to_dval (M.find k s), s)
  | OPut,    [DInt k; v]     => (DUnit, M.add k v s)
  | ODelete, [DInt k]        => (DUnit, M.remove k s)
  | _, _                     => (Dstuck, s)
  end.

(** ** The reference interpreter. Structurally recursive on [t], hence total. *)
Fixpoint run (env : list dval) (t : tm) (s : state) : dval * state :=
  match t with
  | Ret v        => (eval_val env v, s)
  | Bind t1 t2   => let '(x, s') := run env t1 s in run (x :: env) t2 s'
  | Perform o args => handle o (map (eval_val env) args) s
  | MatchOpt scrut none some =>
      match eval_val env scrut with
      | DNone   => run env none s
      | DSome x => run (x :: env) some s
      | _       => (Dstuck, s)
      end
  end.

Definition run_top (t : tm) : dval * state := run [] t (M.empty dval).

(** The order-independent observable: result value + sorted key/value bindings. *)
Definition observe (t : tm) : dval * list (Z * dval) :=
  let '(r, s) := run_top t in (r, M.elements s).

(** ** The slice-1 example program: increment the [option]-valued counter at a key.
    [incr_at k] = get k; if absent put (succ zero)=1 else put (succ x). *)
Definition incr_at (k : Z) : tm :=
  Bind (Perform OGet [VInt k])
       (MatchOpt (VVar 0)
          (Perform OPut [VInt k; VSucc VZero])
          (Perform OPut [VInt k; VSucc (VVar 0)])).

(** The closed spike term used to validate the extraction->codegen bridge (Step 1). *)
Definition prog0 : tm := incr_at 7.
