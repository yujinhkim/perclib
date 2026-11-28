# Random revealed sets and amalgamation

`Correlation/Gladkov/RandomAmalgam` extends the fixed-revealed-set result to a
countably indexed random family under an explicit self-determination condition.
It is a sufficient case of the independence argument, not the complete
sequential decision-tree lemma.

## Hypotheses and conclusion

The family `Sfam : ℕ → Set ι` and index map `idx` select the revealed set
`Sfam (idx ω)`. The assumptions are measurability of `idx` and of each
coordinate-revelation event, together with `SelfDetermined`: if two
configurations agree on all revealed coordinates, in both copies, they select
the same revealed set. This makes each fibre `idx = n` invariant under flipping
the copies off `Sfam n`.

The theorem `prodBernoulli_random_amalgam_indep` partitions the probability
space into those disjoint measurable fibres. Every summand is the actual
measure of a fibre, not a borrowed indicator weight. On each fibre, the flip
used in the deterministic proof converts the two amalgamations into the two
independent original copies and preserves their probabilities. Consequently
the amalgamations are independent, each has law `prodBernoulli q`, and their
joint push-forward law is the product of two copies of that law.

## Non-vacuity and counterexamples

`RandomAmalgamExample` proves the assumptions for a genuinely random one-step
exploration: the second coordinate is revealed exactly when the first copy is
open at the first coordinate. The first coordinate is revealed in both cases,
so the selection is self-determined.

`RandomAmalgamCounterexample` proves that measurability alone is insufficient.
On one coordinate with parameter $1/2$, a different measurable selection gives
the second amalgamation mass $1/4$ at the singleton-open event, rather than the
original law's mass $1/2$. A second example demonstrates that being produced
by an assign-before-revealing decision tree does not imply `SelfDetermined`.
Thus the sufficient condition here must not be confused with the general
procedural hypothesis in the sources.

## Remaining work

The actual finite-tree/transcript formulation, unique reconstruction along a
transcript, and its preservation of product probabilities are not formalized.
The countable-family theorem also does not resolve the general uncountable
family case, the DFS realization, the decision-tree HK or vdBK inequalities,
or the full Gladkov inequality I.2.7. The stronger joint-independence operation
used in later steps is likewise outside this packet.

Sources checked during review:
[Gladkov, Lemma 3.1](https://arxiv.org/html/2408.08457v2#S3.Thmtheorem1) and
[Gladkov–Zimin, Lemma 4.2](https://arxiv.org/html/2404.08873v2#S4.Thmtheorem2).
All 16 principal exported declarations were independently elaborated and have
only `propext`, `Classical.choice`, and `Quot.sound` as axioms.

## Subsequent finite-transcript result

The [finite decision-tree note](CRITICAL_LRP_DECISION_TREE_AMALGAM.md) now
records a genuine transcript/reconstruction proof of the finite lemma. The
countable self-determination theorem in this file remains a distinct sufficient
case, not a substitute for it. The earlier gap statement concerns what was
available at that time. The full Gladkov inequality, infinite-graph analogue,
and later decision-tree applications still remain separate open inputs.
