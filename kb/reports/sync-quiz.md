# KB sync quiz (Phase 6)

Three hard questions about what was built in Phase 4-5, to confirm the KB now conveys reality. A fresh
KB-only subagent answers; gaps get closed.

1. Is `Runtime_KV_refines` a Rocq `Axiom`? If not, what is it, where does it live, and how is it validated?
   What does `Print Assumptions incr_correct` report, and is that consistent with the answer?
2. `kb/spec/effir.md` lists `VPrim prim (list val)` and a general `Match val (list branch)` with a
   `typecheck_ir.ml`. Does slice 1 implement those? What does it implement instead, and which KB file states
   the divergence authoritatively?
3. How many programs does the differential test actually compare, over how many states, and which edge
   classes are asserted-covered? Which of P7's three state laws are proven, and does `incr_correct` say
   anything about keys other than the one incremented?

## Result
A fresh **KB-only** subagent scored **3/3**; consistency confirmed — every aspirational spec file carries a
slice-1 banner linking to [[slice1-status]], which "governs for slice 1". One gap found and **fixed**: the
asserted edge-class set was framed inconsistently (slice1-status T2/T4/T5 vs edge-cases T2/T5/T6/T7);
`edge-cases.md` now states the authoritative asserted set (T2/T4/T5 counted, T7 structural, T8 fault-injected,
T6 occurs-but-not-counted, T1 N/A). Phase 6 declared done.
</content>
