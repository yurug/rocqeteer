(** * Codec pilot — a typed binary encoding whose round-trip is PROVEN (property P8).

    The realistic A3 target (kb/domain/prd.md): a `data-encoding`-style typed codec. Rocq
    owns the FORMAT — descriptors [enc], a typed-value relation, and [encode]/[decode] over a
    token stream — and proves [decode (encode v) = v] composably. OCaml owns the runtime: a
    GADT [_ enc] over real [bytes] with NO Obj.magic (runtime/codec.ml), property-tested to
    round-trip. This is the report's "reference-first" trust policy (§18.3): the format is
    proven; the bytes realizer is tested. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

From Rocqeteer Require Import EffIR.   (* reuse [dval] as the value space (DInt / DPair) *)

(** Encoding descriptors: a Z (token), or a pair of encodings. *)
Inductive enc : Type := EInt | EPair (e1 e2 : enc).

(** Which [dval]s a descriptor accepts. *)
Fixpoint typed (e : enc) (v : dval) : Prop :=
  match e, v with
  | EInt, DInt _ => True
  | EPair e1 e2, DPair a b => typed e1 a /\ typed e2 b
  | _, _ => False
  end.

(** Encode to a token stream ([list Z]); [decode] consumes a prefix and returns the rest. *)
Fixpoint encode (e : enc) (v : dval) : list Z :=
  match e, v with
  | EInt, DInt z => [z]
  | EPair e1 e2, DPair a b => encode e1 a ++ encode e2 b
  | _, _ => []
  end.

Fixpoint decode (e : enc) (ts : list Z) : option (dval * list Z) :=
  match e with
  | EInt => match ts with z :: rest => Some (DInt z, rest) | [] => None end
  | EPair e1 e2 =>
      match decode e1 ts with
      | Some (a, rest1) =>
          match decode e2 rest1 with
          | Some (b, rest2) => Some (DPair a b, rest2)
          | None => None
          end
      | None => None
      end
  end.

(** ** Composable round-trip: decoding [encode v] followed by any suffix [ts] returns [v]
    and leaves exactly [ts]. The [++ ts] generalization is what makes the pair case go
    through by induction. This is property P8 for the reference format. *)
Theorem decode_encode : forall e v ts,
  typed e v -> decode e (encode e v ++ ts) = Some (v, ts).
Proof.
  induction e as [| e1 IH1 e2 IH2]; intros v ts H.
  - destruct v; try contradiction. reflexivity.
  - destruct v as [| | | | | a b | |]; try contradiction.
    destruct H as [H1 H2]. simpl encode. rewrite <- app_assoc. simpl decode.
    rewrite (IH1 a (encode e2 b ++ ts) H1).
    rewrite (IH2 b ts H2).
    reflexivity.
Qed.

(** The headline round-trip: [decode e (encode e v) = Some (v, [])]. *)
Corollary roundtrip : forall e v, typed e v -> decode e (encode e v) = Some (v, []).
Proof. intros e v H. rewrite <- (app_nil_r (encode e v)). apply decode_encode; exact H. Qed.

(** Anti-vacuity: a wrong decoder that drops the first token does NOT round-trip a single
    int — so [roundtrip] genuinely constrains [decode] (kb/architecture/decisions/adr-0005-anti-vacuity.md). *)
Definition decode_bad (e : enc) (ts : list Z) : option (dval * list Z) :=
  match ts with _ :: z :: rest => Some (DInt z, rest) | _ => None end.

Theorem decode_bad_breaks : decode_bad EInt (encode EInt (DInt 7)) <> Some (DInt 7, []).
Proof. cbn. discriminate. Qed.

Print Assumptions roundtrip.
