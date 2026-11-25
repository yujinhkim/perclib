# Monotone moments and capped cutoff flux

## Monotone cluster moments

`CountableProduct/MonotoneMoments.lean` uses the native thresholded-uniform-mark
coupling, not a replacement bond configuration.

`lintegral_clusterVol_mono_of_le` proves, for pointwise ordered edge laws,

```text
∫⁻ |K_o(π)| ≤ ∫⁻ |K_o(κ)|.
```

Tonelli expands cluster volume into connection probabilities; each is increasing
by `edgeMeasure_mono_of_le`. This is true in `ℝ≥0∞`, including top values.
`lintegral_clusterVol_sq_mono_of_le` gives the analogous result for second
moments by the same argument applied to intersections of connection events.

The other two statements transfer finite second and joint-window moments from a
dominating law. The assumptions are finite expected cluster volume and equality
of that mean between roots; translation invariance gives the latter. These are
not claims that every inhomogeneous graph satisfies the cubic second-moment
estimate. That estimate is disproved by the rational two-level-star example in
`SecondMoment`.

This makes the remaining sharpness obligation concrete: find a dominating
subcritical law with a genuinely finite mean. It does not merely change a
second-moment assumption into an unmentioned first-moment assumption.
`CriticalLRP/CutoffDominated.lean` now builds the concrete reduced-parameter
law of Definition I.1.5 and proves this dominance at the native law level. Its
second and joint moment transfers use the new homogeneous moment machinery.
The only remaining step is the finite upstream mean itself.
The binary-tree module in `CRITICAL_LRP_SHARPNESS_MODELS.md` provides a
nonzero concrete example with exact finite subcritical mean and with zero root
percolation probability but infinite mean at `log 2`. It confirms why this
input is not reducible to absence of an infinite cluster; it does not provide
the required lattice cutoff bound.
The companion `CriticalLRP/CutoffLimit` module proves that the cutoff
expected cluster volume increases to the uncut expected cluster volume. A
uniform radius bound consequently goes back to the uncut mean. Conversely,
uncut infinitude gives cutoff divergence in `ℝ≥0∞`, without erasing the
finite-mean or infinite-mean input.

`PowerLawHighTemp` now proves finite mean for the summable power-law lattice
when `β M < 1`, with `M` the total profile mass, and transfers this conclusion
to smaller pair intensities. This is a proved high-temperature interval, not the
whole subcritical interval below `β_c`. The reduced critical parameter needed
by the dominance chain is still not covered.

## Capped flux majorant

`RussoInf/CutoffFluxMajorant.lean` proves a right-endpoint dominator for the
cutoff pivotal flux. The event that an edge touches the root cluster is
increasing, so its probability increases with the radius. A fixed mean-finite
parameter at the right endpoint therefore supplies a summable dominating
sequence through the existing per-vertex degree bound.

`hasDerivAt_cutoffClusterVol_of_majorant` proves the derivative of the **capped**
cutoff functional without an independent uniform-window or uniform-total-mass
hypothesis. Its endpoint finite mean is retained as `hvol`; its termwise
continuity and the window-flux measurability are retained as `hcontterm` and
`hmeas`. `cutoff_fluxWeight_le` separately gives the uniform mass comparison.

It does not uncap the derivative, prove the genuine sharpness estimate, or
supply the remaining regularity assumptions. It should not be read as completing
Lemma I.4.1 or any assertion of Corollary I.4.8.

## A real interface counterexample

`edgeLen_loop` proves that diagonal pairs have length zero.
`modelProfile_hprof_fails` then shows that the intended power-law profile does
not satisfy the nonnegativity hypothesis of `cutoffPiFamily` on all unordered
pairs, because at a diagonal pair the cutoff difference is negative.

Consequently, the existing cutoff-family hypothesis is not instantiated by the
source profile on this loop-carrying configuration space. The new proof keeps
this profile manipulation and the actual source model distinct; it does not
present the cutoff derivative as already specialized to the paper's model.
The native `CutoffKernel.cutoffSymKernel`, which discards diagonal pairs, remains
the appropriate source-law interface for the cutoff lemmas proved elsewhere.

## Verification

The two modules pass focused `lake build --wfail` compilation. Every focused
`#print axioms` audit, including the profile counterexample, reports only
`propext`, `Classical.choice`, and `Quot.sound`. These are local checks, not CI.
