---
id: tower-rationale
type: concept
summary: Why effect towers matter even though they leave the mode-F production binary byte-identical — the certified artifact is the theorem about the binary, not the binary; towers act on the theorem's hypotheses (assurance dial), its evidence (N-version cross-validation), the marginal TCB cost of future effects (O(#kernels) not O(#effects)), and the platform's credibility (the chosen-for-redoq critique answered by a theorem). Ratified in discussion 2026-07-19.
domain: architecture
last-updated: 2026-07-19
depends-on: [adr-0016-effect-towers, adr-0004-trust-model]
refines: []
related: [plan-towers, runtime-manifest]
---
# Why towers, if the certified binary doesn't change? (the rationale, 2026-07-19)

The sharp form of the objection (user, 2026-07-19, after C1): *mode F is the production
path; C1 changed neither redoq's code nor its assumption set; if the towers stop here
they are intellectual decoration.* That concession is CORRECT — and the answer is that
"the certified artifact" is the wrong unit of account. **Rocqeteer sells a theorem
about a binary, not a binary; a theorem has hypotheses; the towers act on the
hypotheses.** Four concrete effects:

## 1. The trust claim becomes a dial — and the second position is shippable
Pre-tower there is one product: fast binary + "believe the fused realizer" (for Expiry:
130 lines with liveness boundary, lazy deletion, clock coupling). Post-tower there are
two: the same fast binary (mode F), or a **mode-K build** where that semantic surface is
a theorem and the residual trust is a ~15-line dictionary handler with no deadline logic
and no clock. A consumer who values assurance over throughput — auditor, regulator,
skeptical reviewer — can be handed mode K TODAY. Same functional claim, strictly weaker
hypotheses: that IS a new certified artifact. Certified artifacts are (binary, claim)
pairs, and towers add a pair.

## 2. Mode F's unchanged assumption gains stronger evidence
`Runtime_KV_refines` is the same statement, but now cross-validated by an independent
implementation of the same semantics sharing no code: fused realizer ≡ reference
(diff suites) and reference ≡ kernel+proven-elaboration (theorem + mode-K diff suites).
A bug in the fused realizer must fool both. An N-version argument, not a proof — but
for the TRUSTED half of the system, better evidence is exactly what "better" means
([[adr-0004-trust-model]]: prove the provable, TEST the trusted).

## 3. The marginal TCB cost of future effects drops to zero
Pre-tower, every convenience effect = new trusted realizer + new manifest assumption +
new diff suite: TCB growth linear in #effects — exactly how the op list got
Redis-shaped. Post-tower, a new high-level effect is a proven elaboration over existing
kernels: **no new realizer, no new assumption**. Future apps add kernel families only
where physics demands (fd I/O, sockets); conveniences become theorems. The tower bends
TCB growth from O(#effects) to O(#kernels), and #kernels stays small.

## 4. It converts the founding critique into a theorem
"The effects were chosen for redoq" is answered by `elab_simulates`, not by prose:
deadlines/cache/journal are not primitive commitments of the IR — here is the proof.
CompCert's value was never that binaries behaved differently; it is that "the compiler
is correct" left the list of things one must believe. Same move, per layer.

## What makes it bite (else it stays latent)
- C2 finishes the discharge: 12 ops → 7 irreducible (kernel) in mode K.
- Give redoq a **mode-K CI leg** so ITS certificate can cite it; plausibly run the
  public kill-9 demo in mode K (assurance is the product there; nobody benchmarks a
  demo) while benchmarks stay mode F.
- Quantify the dial: measure mode K's cost on redoq's bench so "performance option"
  is a number, not an adjective (invariant 3: measure, never assert).

## Agent notes
> When someone asks "what did the towers change?", do NOT answer with mode-F behavior
> (nothing, by design). Answer with the four items above, in order, and concede the
> concession first — it is what makes the rest credible.
