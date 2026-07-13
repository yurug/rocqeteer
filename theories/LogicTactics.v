(** * LogicTactics — wp_step / wp_auto / wp_store (R14, adr-0015 §Decision 4).

    Ltac1, stdlib only. [wp_step] is the syntax-directed application of the Logic.v
    rules; [wp_auto] repeats it and tries the routine side-condition discharges
    (lia / byte-and-key equality via congruence); [wp_store] simplifies the
    StoreAssert layer under M.add / M.remove / M.empty.

    Deliberately a TOOLKIT, not full automation (adr-0015): Match splits on values of
    unknown shape and Repeat/Fold invariants remain user-supplied. Every reduction is
    whitelisted [cbn] — no blanket [simpl], and NEVER vm_compute on open terms
    (theories/Prims.v header). *)

From Stdlib Require Import ZArith List String Ascii Bool Lia.
From Rocqeteer Require Import EffIR StoreAssert Logic.
Import ListNotations.
Local Open Scope Z_scope.

(** Discharge an [eval_val env a = shape] side condition when the argument val is
    closed enough (literals, or vars whose env slot is exposed). *)
Ltac wp_val := first [ reflexivity | eassumption ].

(** Reduce the freshly exposed postcondition application: beta for the Q lambdas,
    iota for the outcome matches of [wp_bind]'s split shape, and delta ONLY on the
    small evaluation helpers ([eval_val]/[nth] for de Bruijn lookups, [push_env]/
    [fold_left] for payload pushes, the §3 result views) — FMapAVL and the
    interpreter itself stay folded. *)
Ltac wp_simpl :=
  cbn beta iota delta [eval_val nth push_env fold_left
                       get_view del_view deadline_view opt_to_dval].

(** One syntax-directed step: apply the Logic.v rule for the head constructor,
    discharging the evaluation side conditions that are decidable on the spot. *)
Ltac wp_step :=
  lazymatch goal with
  | |- wp _ (Ret _) _ _                        => apply wp_ret
  | |- wp _ (Bind _ _) _ _                     => apply wp_bind
  | |- wp _ (Perform OThrow (_ :: _)) _ _      => apply wp_throw
  | |- wp _ (Perform OAsk _) _ _               => apply wp_ask
  | |- wp _ (Perform ONow _) _ _               => apply wp_now
  | |- wp _ (Perform OTrace (_ :: nil)) _ _    => apply wp_trace
  | |- wp _ (Perform OJournal (_ :: nil)) _ _  => apply wp_journal
  | |- wp _ (Perform OGet (_ :: nil)) _ _      => eapply wp_get; [wp_val |]
  | |- wp _ (Perform OPut (_ :: _ :: nil)) _ _ => eapply wp_put; [wp_val |]
  | |- wp _ (Perform ODelete (_ :: nil)) _ _   => eapply wp_delete; [wp_val |]
  | |- wp _ (Perform OGetDeadline (_ :: nil)) _ _ =>
        eapply wp_get_deadline; [wp_val |]
  | |- wp _ (Perform OSetDeadline (_ :: _ :: nil)) _ _ =>
        first [ eapply wp_set_deadline_some; [wp_val | wp_val |]
              | eapply wp_set_deadline_none; [wp_val | wp_val |] ]
  | |- wp _ (Perform OCacheGet (_ :: nil)) _ _ => eapply wp_cache_get; [wp_val |]
  | |- wp _ (Perform OCachePut (_ :: _ :: nil)) _ _ =>
        eapply wp_cache_put; [wp_val |]
  | |- wp _ (Prim _ _) _ _                     => apply wp_prim
  | |- wp _ (Match _ _ _) _ _                  =>
        first [ eapply wp_match_here; [reflexivity |]
              | eapply wp_match_skip; [reflexivity |]
              | apply wp_match_default ]
  end;
  wp_simpl.

(** Simplify the StoreAssert layer: resolve M.find over add/remove/empty under key
    (in)equality (congruence discharges the side conditions), expose find_live via
    the assertion definitions when present, and settle liveness ifs whose test is a
    literal. Aggressive by design — it is the dedicated assertion simplifier. *)
Ltac wp_store :=
  unfold live_at, gone_at, maps_to, absent in *;
  repeat first
    [ rewrite find_add_eq
    | rewrite find_add_neq by congruence
    | rewrite find_remove_eq
    | rewrite find_remove_neq by congruence
    | rewrite find_empty
    | rewrite live_no_deadline
    | match goal with
      | H : M.find ?k ?s = _ |- context [find_live ?t ?k ?s] =>
          unfold find_live; rewrite H
      | H : find_live ?t ?k ?s = _ |- context [find_live ?t ?k ?s] =>
          rewrite H
      end ];
  try reflexivity.

(** Routine finisher for postcondition goals: conjunction splitting plus the standard
    dischargers. Never fails. *)
Ltac wp_finish :=
  wp_simpl;
  repeat split;
  try reflexivity; try assumption; try lia; try congruence.

(** The driver: step as far as the syntax directs, then try to finish. Loop
    invariants, Match splits on unknown shapes, and genuinely semantic side
    conditions are left to the user. *)
Ltac wp_auto :=
  repeat wp_step;
  try wp_finish.
