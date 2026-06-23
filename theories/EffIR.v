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

(** ** Effect operations: KV (Get/Put/Delete), [OThrow] (Error), [OAsk] (Env), [OTrace]
    (Trace), and [OCacheGet]/[OCachePut] (Cache — a memo store kept OUT of [observe], so it
    is observationally invisible) — kb/spec/effect-signatures.md. *)
Inductive op : Type :=
  | OGet | OPut | ODelete | OThrow | OAsk | OTrace | OCacheGet | OCachePut.

(** The result of running a computation: a normal value, or an error that aborted it.
    This is what lets [Bind] short-circuit on [OThrow] (the Error effect). *)
Inductive outcome : Type := ORet (v : dval) | OErr (e : dval).

(** ** Effectful computations. [Bind t1 t2] binds the result of [t1] at de Bruijn 0 in
    [t2]; [MatchOpt] is the slice-1 match form (scrutinee is an [option]; the [some]
    branch binds the payload at de Bruijn 0). *)
Inductive tm : Type :=
| Ret      : val -> tm
| Bind     : tm -> tm -> tm
| Perform  : op -> list val -> tm
| MatchOpt : val -> tm -> tm -> tm
| Repeat   : nat -> tm -> tm.   (* bounded loop: run [body] [n] times (the report's for_i / fuel recursion) *)

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

(** ** The [world]: ALL ambient effect state bundled into one record, so adding an effect
    adds a FIELD here rather than another parameter to [run] (the refactor that motivated
    the Trace iteration). [kv] is the KV map, [ctx] the read-only Env context, [trace] the
    Trace log stored newest-first (reversed to chronological by [observe]). *)
Record world : Type := mkWorld {
  kv    : state;
  ctx   : dval;
  trace : list dval;
  cache : state;       (* memo store; deliberately NOT exposed by [observe] *)
}.

Definition set_kv    (w : world) (m : state)     : world := mkWorld m w.(ctx) w.(trace) w.(cache).
Definition set_trace (w : world) (l : list dval) : world := mkWorld w.(kv) w.(ctx) l w.(cache).
Definition set_cache (w : world) (c : state)     : world := mkWorld w.(kv) w.(ctx) w.(trace) c.

(** ** Pure KV handler over the map: the reference semantics of the KV operations. *)
Definition handle_kv (o : op) (args : list dval) (s : state) : dval * state :=
  match o, args with
  | OGet,    [DInt k]        => (opt_to_dval (M.find k s), s)
  | OPut,    [DInt k; v]     => (DUnit, M.add k v s)
  | ODelete, [DInt k]        => (DUnit, M.remove k s)
  | _, _                     => (Dstuck, s)
  end.

(** ** The reference interpreter, threading one [world]. Structurally recursive on [t],
    hence total. [Bind] short-circuits on abort ([OErr]); [OThrow e] aborts; [OAsk] reads
    [ctx]; [OTrace v] appends [v] to the log; KV ops update [kv]. *)
Fixpoint run (env : list dval) (t : tm) (w : world) : outcome * world :=
  match t with
  | Ret v        => (ORet (eval_val env v), w)
  | Bind t1 t2   =>
      match run env t1 w with
      | (ORet x, w') => run (x :: env) t2 w'
      | (OErr e, w') => (OErr e, w')   (* abort: the continuation does not run *)
      end
  | Perform o args =>
      let vs := map (eval_val env) args in
      match o with
      | OThrow => (OErr (nth 0 vs Dstuck), w)
      | OAsk   => (ORet w.(ctx), w)
      | OTrace => match vs with
                  | [v] => (ORet DUnit, set_trace w (v :: w.(trace)))
                  | _   => (ORet Dstuck, w)
                  end
      | OCacheGet => match vs with
                     | [DInt k] => (ORet (opt_to_dval (M.find k w.(cache))), w)
                     | _        => (ORet Dstuck, w)
                     end
      | OCachePut => match vs with
                     | [DInt k; v] => (ORet DUnit, set_cache w (M.add k v w.(cache)))
                     | _           => (ORet Dstuck, w)
                     end
      | _      => let '(r, s') := handle_kv o vs w.(kv) in (ORet r, set_kv w s')
      end
  | MatchOpt scrut none some =>
      match eval_val env scrut with
      | DNone   => run env none w
      | DSome x => run (x :: env) some w
      | _       => (ORet Dstuck, w)
      end
  | Repeat n body =>
      (* run [body] [n] times, threading the world; an abort stops the loop. The inner
         [loop] recurses on the fuel [m]; the calls to [run env body] are on a strict
         subterm of [Repeat n body], so the outer fixpoint stays structurally guarded. *)
      (fix loop (m : nat) (w0 : world) {struct m} : outcome * world :=
         match m with
         | O    => (ORet DUnit, w0)
         | S m' => match run env body w0 with
                   | (ORet _, w1) => loop m' w1
                   | (OErr e, w1) => (OErr e, w1)
                   end
         end) n w
  end.

(** Initial world: empty store, the given [c] context, empty trace, empty cache. *)
Definition init_world (c : dval) : world := mkWorld (M.empty dval) c [] (M.empty dval).

Definition run_top (c : dval) (t : tm) : outcome * world := run [] t (init_world c).

(** The observable: outcome + sorted key/value bindings + the trace in chronological order. *)
Definition observe (c : dval) (t : tm) : outcome * list (Z * dval) * list dval :=
  let '(r, w) := run_top c t in (r, M.elements w.(kv), rev w.(trace)).

(** Like [observe] but from a custom initial KV state [s] (and context [c]); the single
    entry point the differential tests use (they seed a non-empty state). *)
Definition observe_full (c : dval) (s : state) (t : tm)
  : outcome * list (Z * dval) * list dval :=
  let '(r, w) := run [] t (mkWorld s c [] (M.empty dval)) in (r, M.elements w.(kv), rev w.(trace)).

(** ** The slice-1 example program: increment the [option]-valued counter at a key.
    [incr_at k] = get k; if absent put (succ zero)=1 else put (succ x). *)
Definition incr_at (k : Z) : tm :=
  Bind (Perform OGet [VInt k])
       (MatchOpt (VVar 0)
          (Perform OPut [VInt k; VSucc VZero])
          (Perform OPut [VInt k; VSucc (VVar 0)])).

(** The closed spike term used to validate the extraction->codegen bridge (Step 1). *)
Definition prog0 : tm := incr_at 7.
