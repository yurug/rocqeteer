---
id: adr-0015-program-logic
type: decision
summary: R14 — a SHALLOW weakest-precondition layer over the existing run (no second semantics, invariant 1 intact): proven-sound rules per constructor/op/prim, a keyed store-assertion library with liveness lemmas, invariant rules for Repeat/Fold, and wp_* tactics — enabling ∀-quantified program theorems; vm_compute instance proofs remain the regression corpus; Iris/stdpp stay out (dep budget).
domain: architecture
last-updated: 2026-07-13
depends-on: [effir, adr-0001-first-order-ast, adr-0011-time-and-expiring-store, adr-0012-list-elimination, adr-0013-journal-effect]
refines: []
related: [adr-0014-wf-checker, adr-0009-vprim-registry]
---
# ADR-0015 — R14: a program logic for EffIR (the road to quantified specs)

## Context
Every consumer command theorem today is a `vm_compute` equation about one closed run — adversarially
placed, mutant-guarded, and differentially extended, but never universally quantified. The consumer's
replay property (its P4) is likewise per-command instances plus general composition lemmas; its
crown-jewel form — ∀ reachable executions, replay = live — needs ∀-quantified per-command lemmas that
`vm_compute` cannot produce (it only decides closed terms). Direct symbolic execution of `run` by
`destruct`/`simpl` blows up: branches over dvals, Match arm lists, prim options, FMapAVL internals, and
the documented conversion traps. What is missing is a PROGRAM LOGIC: compositional reasoning rules over
EffIR programs with an abstract store.

Constraints: invariant 1 (ONE IR, one semantics — no second interpreter, no instrumented twin as the
spec); dependency budget (NO Iris/stdpp/equations — rocq-stdlib only); the concrete-instance corpus and
its CI value must not be weakened; proofs must survive the known conversion-toxicity traps.

## Decision
1. **Shallow embedding, `run` stays the only truth.** Define
   `wp (env : list dval) (t : tm) (Q : outcome -> world -> Prop) : world -> Prop
      := fun w => let '(o, w') := run env t w in Q o w'`
   — definitionally a statement about `run`; adequacy is trivial and invariant 1 is untouched. The value
   of the milestone is NOT this definition but the RULE LIBRARY proven over it and the tactics that
   apply it. Hoare-triple sugar `{{ P }} t {{ Q }}` unfolds to `forall w, P w -> wp env t Q w`.
2. **One sound rule per construct** (each a lemma proven against `run`, once):
   - `wp_ret`, `wp_bind` (the continuation rule quantifies the intermediate dval and extends env),
     `wp_perform_*` for all 12 ops (store ops phrased via the assertion layer of §3; ONow/OAsk/OTrace/
     OJournal/OThrow/cache each with their exact world transition), `wp_prim` (one spec lemma per prim,
     15, mirroring `apply_prim`), `wp_match` (per-branch rules via `match_pat` inversion helpers +
     the default case), `wp_repeat` (invariant rule, index-carrying), `wp_fold` (list-invariant rule
     over the processed prefix and accumulator, with the OErr short-circuit escape clause),
     error-propagation rules for Bind.
3. **A keyed store-assertion library** (bespoke, minimal — NOT separation logic):
   `k ↦[t] (v, dl)` (find-based binding assertions), `k ∉[t] s` (absent-or-expired at instant t),
   with update lemmas over `M.add`/`M.remove`/`M.find` under decidable key (in)equality side
   conditions, and the LIVENESS lemmas at the boundary (`now <=? d` both sides — the validated rule).
   FMapAVL internals stay Opaque; every lemma goes through the find/add/remove interface only.
4. **Tactics**: `wp_step` (syntax-directed application of the §2 rules), `wp_auto` (repeat wp_step +
   side-condition discharge via `lia`/byte-equality decision), `wp_store` (assertion-layer
   simplification). Ltac1, stdlib only. Match splits and loop invariants remain user-supplied — this
   is a proof TOOLKIT, not full automation.
5. **The instance corpus stays.** vm_compute golden theorems remain the regression armor and the
   anti-vacuity floor; general theorems are ADDITIVE. House anti-vacuity applies to general theorems
   too: each ships inhabitance (the existing concrete instances discharge it) and must be shown to
   FAIL on an existing mutant (e.g. the `<`-liveness mutant store falsifies the general GET spec).
6. **What this unlocks downstream (the campaign, phased per the consumer's split rule):**
   B) ∀-quantified specs for the consumer's core commands (its combinator lemmas first);
   C) the remaining surface; D) ∀ "journals iff effective" per command, which composes with the
   ALREADY-GENERAL frame law and run-sequence fold lemma into the crown jewel: ∀ reachable request
   sequences, replay(journal) = live state. NOTE the relational glue for D already exists in general
   form (adr-0013's lemmas) — unary wp per command is sufficient; no relational calculus is needed.
7. **Non-goals, explicit**: separation-logic framing beyond keyed disjointness side conditions;
   concurrency (the semantics is sequential); resource/cost reasoning (invariant 3: measured, never
   proven); any new dependency; any change to `run`, the IR, or the codegen.

## Consequences
- (+) The theorem quality ceiling moves from "adversarially-placed instances" to "∀ keys, values,
  deadlines, instants" — the honest gap named on the public comparison page becomes closable.
- (+) Shallow embedding means zero new trusted surface: a wp theorem IS a run theorem by unfolding.
- (−) The largest proof-engineering investment so far; rule proofs will fight the interpreter's
  branching (mitigations: the Journal.v strong-induction/twin-equation technique, Opaque discipline,
  the documented Strategy-expand antidote for conversion traps).
- (−) Loop-invariant proofs (Fold-heavy programs: the consumer's SET option scanner, MSET, MGET) are
  genuinely hard and land command-by-command; the split rule (a proof exceeding ~2 sessions ships its
  sub-surface) applies throughout the campaign.

## What this means for implementers
- Phase A (this milestone, upstream): theories/Logic.v (wp + triples + ALL §2 rules + §3 assertions),
  theories/LogicDemo.v with TWO ∀-quantified end-to-end program theorems as the acceptance gate —
  suggested: general GET (∀ k v dl now, over any store satisfying k ↦ (v,dl): returns v iff live at
  now, store unchanged) and general SET-clears-deadline (∀ k v w, post has k ↦ (v, None)) — each with
  inhabitance discharged by existing instances and the liveness mutant shown to falsify it. Tactics in
  a separate file. kb/spec updates; make all green; no Admitted/admit/Axiom; explicit witnesses.
- Watch the traps: never vm_compute an open term; Z.of_nat (k + length l) comparisons under big
  literals need Strategy expand (Resp3 lesson, documented in the consumer's tree).
- Rule statements should be BIASED TO THE TACTIC (conclusion-first, side conditions as separate
  premises) — ergonomics is the deliverable; a technically-sound but unusable rule set fails R14.
