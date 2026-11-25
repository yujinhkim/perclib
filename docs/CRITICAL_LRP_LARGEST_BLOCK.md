# Largest block: exact window identity and tail/moment bounds

`Tightness/BlockMaximum.lean` proves the paper's finite-window identity

$$
\sup_{v \in V} |K_v \cap W| = \max_{w \in W} |K_w \cap W|.
$$

It handles clusters disjoint from the window, proves attainment for nonempty windows,
and records the empty-window value separately. The truncated volume at **any** base point
is bounded by the window maximum, which transfers the maximum-cluster tail to an
arbitrary base point without a membership assumption.
`tail_single_of_tailMax_anyV` is the corresponding single-cluster tail estimate.

The elementary cardinality bound and median rule are carefully separated:
`clusterMaxVol ω W ≤ |W|`, and `edianMaxVol ≤ |W| + 1`. On the everywhere-open
configuration the bound is attained, so `|W|+1` is best possible as a universal bound
for the **existing `edianMaxVol` definition**. This is not a statement about the paper's
asymptotic median scaling.

`Tightness/LargestBlockMoment.lean` uses an integer layer cake and the maximum-cluster
tail to prove

$$
\frac{M-1}{e} \le \mathbb E|K_{\max}(W)| \le 10M,
$$
for every nonempty window, where `M = edianMaxVol`. The lower bound uses the existing
Markov argument. The upper bound splits the layers below and above the median and sums
$q^{n+1}$ with $q=e^{-1/(9M)}$, using $M\ge1$.

Neither result assumes a finite cluster moment or a percolation model: the upper mean
estimate uses the explicit `Display28` tail hypothesis, instantiated in source models by
the established long-range universal tightness result. It is not an asymptotic median
estimate.

Integration repaired the layer-cake invocation, the exponential-power normalization,
and final ENNreal arithmetic in the unfinished packet. The definitions-only block module
and downstream mean module both compile strictly with only standard axioms.
