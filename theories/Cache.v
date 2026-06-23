(** * Cache effect — observational invisibility, proven, with anti-vacuity.

    The cache is a memo store kept OUT of the observable. [sample_cache] memoizes the value
    1 at key 0 and writes it to key 1. This file proves the KV result at key 1 is the SAME
    whether the cache HITS (correct memo present) or MISSES (empty) — i.e. caching is
    observationally invisible — and a companion lemma showing the cached value is genuinely
    read (so the invisibility is non-trivial). The OCaml handler (runtime/cache.ml) refines
    this, validated by tests/diff_cache.ml. *)

From Stdlib Require Import ZArith List FMapFacts FMapAVL OrderedTypeEx.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

Module Import CFacts := FMapFacts.WFacts_fun(Z_as_OT)(M).
Opaque M.find M.add M.empty M.remove.

Lemma find_add_same : forall k (v : dval) (s : state), M.find k (M.add k v s) = Some v.
Proof. intros; apply add_eq_o; reflexivity. Qed.

(** Run [sample_cache] from an initial cache [initc] (empty KV/ctx/trace); read key 1. *)
Definition run_cache (initc : state) : option dval :=
  let '(_, w) := run [] sample_cache (mkWorld (M.empty dval) DUnit [] initc) in M.find 1 w.(kv).

(** MISS (empty cache): compute succ zero = 1, write it at key 1. *)
Lemma run_cache_miss : run_cache (M.empty dval) = Some (DInt 1).
Proof.
  unfold run_cache, sample_cache.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv set_cache kv cache].
  rewrite empty_o.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv set_cache kv cache].
  rewrite find_add_same; reflexivity.
Qed.

(** HIT with the correct memo (0 -> 1): use the cached value, write it at key 1. *)
Lemma run_cache_hit : run_cache (M.add 0 (DInt 1) (M.empty dval)) = Some (DInt 1).
Proof.
  unfold run_cache, sample_cache.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv set_cache kv cache].
  rewrite find_add_same.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv set_cache kv cache].
  rewrite find_add_same; reflexivity.
Qed.

(** ** Observational invisibility: a correct HIT and a MISS give the same KV result. *)
Theorem cache_invisible :
  run_cache (M.add 0 (DInt 1) (M.empty dval)) = run_cache (M.empty dval).
Proof. rewrite run_cache_hit, run_cache_miss; reflexivity. Qed.

(** ** Anti-vacuity: a HIT with a DIFFERENT cached value (0 -> 99) yields 99 at key 1 — so
    [sample_cache] genuinely reads the cache, and [cache_invisible] holds precisely because
    the memo (1) matches the computed value, not because the cache is ignored. *)
Theorem run_cache_uses_value :
  run_cache (M.add 0 (DInt 99) (M.empty dval)) = Some (DInt 99).
Proof.
  unfold run_cache, sample_cache.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv set_cache kv cache].
  rewrite find_add_same.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv set_cache kv cache].
  rewrite find_add_same; reflexivity.
Qed.

Print Assumptions cache_invisible.
