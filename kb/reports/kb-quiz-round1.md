# KB quiz — round 1 (Phase 2 exit gate)

Ten difficult questions probing the load-bearing, easy-to-get-wrong parts of the KB. A fresh subagent with
KB-only access answers each; gaps revealed are fixed before the KB is declared done.

1. Why is the report's HOAS `Prog` (`Op : ∀X, E X → (X → Prog E A) → Prog E A`) rejected, and what
   specifically cannot be done with it on Rocq 9.1? What replaces it?
2. How does an EffIR term reach the codegen, and why is there deliberately no JSON/serialization layer in
   the v1 TCB?
3. What is the precise difference between EffIR's `val` and `tm` layers, and why does keeping them separate
   matter for the reference interpreter?
4. The user asked for software that is "functionally and nonfunctionally correct." What does v1 actually
   deliver for non-functional properties, and what is explicitly NOT delivered?
5. Which functional property is *tested but not proven*, why can it not be proven, and what discipline
   compensates?
6. A developer states a Hoare spec and the proof compiles. What two artifacts must accompany it, and which
   failure mode do they prevent?
7. Why is `Z` (zarith) the default numeric realizer rather than `int63`, and under exactly what conditions
   may a bounded `int63` realizer be used?
8. Name at least five CI conditions that fail the build because they represent a silent trust expansion.
9. What must be true before "breadth" (a second effect family or runtime module) may begin? Name the slice
   and its definition of done.
10. An effect operation is performed at runtime but no handler is installed for it. What happens, and
    where/how is it turned into something safe for a public API?

## Scoring (result)
A fresh subagent with **KB-only** access answered all ten.
- **SCORE: 10/10** confidently answerable from the KB.
- **Navigability:** indexes (`INDEX.md`, `indexes/by-task.md`, per-dir `INDEX.md`) routed cleanly, no dead
  ends; all followed links resolved. Multi-hop answers (Q1/Q7/Q10) were frictionless thanks to glossed links.
- **Gaps:** none material. Two cosmetic notes addressed/accepted:
  1. `INDEX.md` file-count line generalized so it doesn't drift as `reports/` grows. (fixed)
  2. Exact EffIR Rocq constructor names are intentionally deferred to slice-1 implementation
     (`spec/effir.md` says so) — a stated deferral, not a gap.

Phase 2 (Knowledge Base) is declared **done**.
</content>
