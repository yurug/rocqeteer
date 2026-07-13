---
id: program-logic
type: spec
summary: The R14 shallow wp layer over run — the wp definition and triple sugar, the proven rule inventory (structural, one per op, one per prim, Match, Repeat/Fold invariant rules), the keyed store-assertion library, the wp tactics, and what remains user-supplied.
domain: spec
last-updated: 2026-07-13
depends-on: [effir, reference-semantics, adr-0015-program-logic, adr-0011-time-and-expiring-store]
refines: []
related: [adr-0013-journal-effect, slice1-status, conv-testing-strategy]
---
# Spec — the EffIR program logic (shallow wp)

## One-liner
`wp env t Q` is **by definition** a statement about `run env t` — a shallow weakest-precondition
layer (zero new trusted surface, invariant "one IR, one semantics" untouched) whose value is the
**rule library proven against `run` once** and the tactics that apply it, enabling ∀-quantified
program theorems where the corpus previously had only vm_compute instances.

## The definition (`theories/Logic.v` §1)
```coq
Definition wp env t (Q : outcome -> world -> Prop) : world -> Prop :=
  fun w => let '(o, w') := run env t w in Q o w'.
Definition triple env P t Q := forall w, P w -> wp env t Q w.   (* env |- {{P}} t {{Q}} *)
```
Adequacy is definitional: `wp_run`/`run_wp` convert between wp facts and `run` equations by
unfolding. `wp_conseq`/`triple_conseq` are the consequence rules.

## Rule inventory (each a lemma proven against `run`, `theories/Logic.v`)
| Construct | Rules | Shape |
|-----------|-------|-------|
| `Ret` | `wp_ret` | conclusion-first: prove `Q (ORet (eval_val env v)) w` |
| `Bind` | `wp_bind`, `wp_bind_err` | THE one Bind shape: continuation postcondition **splits on the outcome** (`ORet x` ⇒ wp of `t2` with `x :: env`; `OErr e` ⇒ straight into Q) — error propagation falls out |
| `OGet` | `wp_get` + `wp_get_live`/`wp_get_gone` | base rule yields `get_view (find_live now k kv)`; derived rules take a `live_at`/`gone_at` assertion |
| `OPut` | `wp_put` | post-world `set_kv w (M.add k (v, None) kv)` — deadline cleared by shape |
| `ODelete` | `wp_delete` + `_live`/`_gone` | `del_view` result; world gets `M.remove` |
| `OGetDeadline` | `wp_get_deadline` + `_live`/`_gone` | `deadline_view` nested-option result |
| `OSetDeadline` | `wp_set_deadline_some`/`_none` + 4 live/gone splits | both payload shapes; true iff a live binding was modified |
| `ONow`/`OAsk`/`OThrow` | `wp_now`/`wp_ask`/`wp_throw` | exact `run` transitions; `OThrow` lands in `Q (OErr …)` |
| `OTrace`/`OJournal` | `wp_trace`/`wp_journal` | newest-first append; journal entry stamped `now_ms` |
| `OCacheGet`/`OCachePut` | `wp_cache_get`/`wp_cache_put` | the memo store, `M.find`/`M.add` |
| `Prim` | `wp_prim` + one spec lemma per prim (16, incl. `PListSnoc`) | mirror `apply_prim`; pure, world unchanged |
| `Match` | `wp_match_here`/`wp_match_skip`/`wp_match_default` | first-match-wins, syntax-directed; + 8 `match_pat_*_inv` inversion helpers (one per pattern) and `ascii_list_eqb_eq` reflection |
| `Repeat` | `wp_repeat_inv` | index-carrying invariant `I : nat -> world -> Prop`; OErr escape straight into Q |
| `Fold` | `wp_fold_inv`, `wp_fold_empty` | invariant `I : list dval -> dval -> world -> Prop` over processed-prefix × accumulator; OErr escape; non-DList = empty fold |

Nested-fix constructs go through the Journal.v twins (`try_branches`/`repeat_loop`/`fold_elems` +
`run_*_eq`) with local one-step equations — no cbn into anonymous fixes, never vm_compute on open
terms (the `theories/Prims.v` conversion-toxicity note).

## Store assertions (`theories/StoreAssert.v`, adr-0015 §Decision 3)
`maps_to k v dl s` (physical `M.find` binding) · `absent` · `live_at t k v dl s` / `gone_at t k s`
(the `find_live` view every op sees) · liveness-boundary lemmas BOTH sides of `now <=? d`
(`live_at_deadline`, `dead_past_deadline`, `live_iff`/`dead_iff`) · add/remove/find update lemmas
under decidable string-key (in)equality · bridges `find_live_maps_to`, `live_at_intro/elim`,
`gone_at_absent/expired/elim`. All through the FMap **interface** only (stdlib `FMapFacts`) — AVL
internals stay opaque.

## Tactics (`theories/LogicTactics.v`, Ltac1, stdlib only)
- `wp_step` — syntax-directed rule application (discharges `eval_val` side conditions by
  reflexivity/eassumption; tries here/skip/default for Match).
- `wp_simpl` — whitelisted cbn (beta, iota, and delta only on `eval_val`/`nth`/`push_env`/views).
- `wp_store` — assertion-layer simplification over `M.add`/`M.remove`/`M.empty` + key inequality.
- `wp_auto` = `repeat wp_step; try wp_finish` (splits conjunctions, tries lia/congruence).

## What remains USER-SUPPLIED (adr-0015 §Decision 4 — a toolkit, not automation)
- Loop invariants for `Repeat`/`Fold` (and their `I 0`/prefix-`[]` establishment).
- Match splits when the scrutinee's shape is not yet determined (destruct first).
- Genuinely semantic side conditions (liveness at abstract instants, key disequalities).

## Acceptance gate (`theories/LogicDemo.v`)
Two ∀-quantified end-to-end theorems: **general GET** (`get_general`: DSome v iff live at
`now_ms`, world literally unchanged — `w' = w` via record eta, the strongest formulation) and
**general PUT-clears-deadline** (`put_general`: `maps_to k (eval vv) None` + the ∀ k' ≠ k frame
clause). Each with explicit inhabitance witnesses (the TimeStore.v corpus store) and the GET spec
proven **false** under TimeStore.v's `<`-liveness `run_mut` at `now = dl`
(`get_general_falsified_under_mutant`). §7 exercises triple sugar, Match, Repeat and Fold rules
on further general theorems (`repeat_trace_general`, `fold_rebuild_general`).

## Status
The vm_compute instance corpus stays authoritative and untouched (adr-0015 §Decision 5); general
theorems are additive. Downstream: the consumer's ∀-quantified per-command campaign (adr-0015
§Decision 6).

## Known issues (R14 phase B field report, 2026-07-13)
- `wp_step`'s Match arm DIVERGES (spins, not fails) when the scrutinee's `match_pat` is undecided
  on an open term (e.g. a checked-prim result over abstract Z): `reflexivity` on
  `match_pat PSome (apply_prim ...) = Some ?p` ran >7 min. Workaround (consumer CmdSpecs.v
  pttl_spec_wp): counted `do N wp_step` + whitelisted `cbn [map eval_val nth apply_prim]` +
  the prim's in-range rewrite. FIX WANTED next Logic round: guard the Match arm with a
  head-constructor check (fail fast when the scrutinee is not a constructor application).

## Agent notes
> State rules conclusion-first with side conditions as separate premises — `wp_step` depends on
> it. New store ops must add: the base rule (exact `handle_store` branch), live/gone splits, and
> a `wp_step` arm. If a proof needs vm_compute, the term MUST be closed — no exceptions.
