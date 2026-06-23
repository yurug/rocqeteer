(** * Trace effect — the append-only log records events in order, proven, with anti-vacuity.

    [OTrace v] appends [v] to the log; [observe] returns it in chronological order. This file
    proves a concrete program records its events in the right order, and a mutant showing the
    order is load-bearing. The OCaml handler (runtime/trace.ml) refines this, validated by
    tests/diff_trace.ml. *)

From Stdlib Require Import ZArith List FMapFacts FMapAVL OrderedTypeEx.
From Rocqeteer Require Import EffIR Samples.
Import ListNotations.
Local Open Scope Z_scope.

Module Import TFacts := FMapFacts.WFacts_fun(Z_as_OT)(M).
(* Keep the map (incl. elements) opaque so the ignored KV component never blocks reduction. *)
Opaque M.find M.add M.empty M.remove M.elements.

(** [sample_trace] = emit 10; put 1; emit 20 — the trace records [10; 20] in order. *)
Theorem sample_trace_records :
  let '(_, _, tr) := observe DUnit sample_trace in
  tr = [DInt 10; DInt 20].
Proof.
  unfold observe, run_top, sample_trace.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv set_trace kv ctx trace init_world rev].
  reflexivity.
Qed.

(** Anti-vacuity (mutant): emitting in the OTHER order yields a different trace — so the
    "[10; 20]" in [sample_trace_records] genuinely pins the ORDER (adr-0005-anti-vacuity). *)
Definition sample_trace_wrong : tm :=
  Bind (Perform OTrace [VInt 20]) (Perform OTrace [VInt 10]).

Theorem sample_trace_order_matters :
  let '(_, _, tr) := observe DUnit sample_trace_wrong in
  tr <> [DInt 10; DInt 20].
Proof.
  unfold observe, run_top, sample_trace_wrong.
  cbn [run eval_val map nth opt_to_dval handle_kv set_kv set_trace kv ctx trace init_world rev].
  discriminate.
Qed.

Print Assumptions sample_trace_records.
