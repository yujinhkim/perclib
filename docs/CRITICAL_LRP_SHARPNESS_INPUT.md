# Supporting limits and minimal thresholds for the sharpness bootstrap

`CriticalLRP/SharpnessInput.lean` isolates two regularity ingredients needed by
the first-moment bootstrap of Lemma I.4.9. It does **not** prove finite upstream
mean at criticality, the full sharpness theorem, or the uncapped cutoff
derivative.

## Exact reduced coefficients and the meaning of uniformity

`MomentMonotonicity/ReducedCoefficients/Main.lean` now proves the exact
reduced-intensity comparison. With `c_r = cutCoeffNN t₀ r`, where the strict
coefficient from Definition I.1.5 is compiled to satisfy `1/2 ≤ c_r < 1` and
tend to `1`, the uncut first moment is the supremum of the reduced-intensity
means. Consequently finiteness at the endpoint is equivalent to a *single
finite uniform bound over the entire coefficient-indexed family*, not to
finiteness of each member. The reduced intensities are also constructed
cofinally using `K(r) → 0`, so `SubcriticalFiniteMean` below an intensity is
exactly termwise finiteness of that family. At criticality, infinitude remains
an explicit premise: no critical uncut mean or hsub family is computed here.
The same file gives the top-safe equivalence between hsub and a finite bound
on `cutMassAtBeta β r 0` that is uniform in `r` at each strictly subcritical β.

`Local.lean` shows why nevertheless only one reduced intensity is needed for
a bounded radius window: the existing cutoff domination is instantiated
first, then `uncutMoment_four_ne_top_of_first` is applied at that reduced
intensity. This proves fourth cutoff moment finiteness on `(0,R]`, and yields
both the second-moment and first-moment off-corner derivatives from one
finite uncut mean at `betaCrit * c`, with `0 < c < 1`. It is a hypothesis on
that point, not a proof of hsub or a uniform critical bound.

`ExactPowerLaw.lean` sharpens the coefficient threshold: at the literal
power-law witness and `R ≥ 2`, domination of the cutoff kernel by `c · J` is
equivalent to `1 - (2/R)^(d+α) ≤ c`. The cheapest coefficient is forced by
the explicit minimal edge of length `2` in the normalized sup norm, not by a
convenient arbitrary choice. No single subcritical coefficient serves all
unbounded radii, and intensities `1 - (2/R)^(d+α)` accumulate at `betaCrit`
up to normalization. So the bounded-window localization is genuine, while
the unrepaired unbounded-range sharpness obligation remains precisely the
reduced family approaching the critical parameter.


## Left continuity in the intensity parameter

For a family `P β : Sym2 V → unitInterval`, nondecreasing below `βc` and
pointwise continuous from the left, `tendsto_lintegral_clusterVol_Iio` proves

```text
∫⁻ |K_o| d(edgeMeasure (P β)) → ∫⁻ |K_o| d(edgeMeasure (P βc))
```

in `ℝ≥0∞`. Infinite means are permitted. The proof reduces to an increasing
sequence of parameters and the already proved monotone convergence of
connection events and expected cluster volume.

`tendsto_lintegral_clusterVol_longRangeMeasure` and its cutoff instance
specialize this to `1 - exp(-β J)`. No kernel profile positivity, diagonal
condition or moment finiteness is needed for these `ℝ≥0∞` statements.

### Why there are separate `toReal` theorems

The real bootstrap uses `F β r = (E_{β,r}|K|).toReal`. Since `toReal ∞ = 0`,
the extended-real limit alone does not imply its `toReal` form at an infinite
endpoint. The separate declarations
`tendsto_toReal_lintegral_clusterVol_longRangeMeasure` and
`tendsto_toReal_lintegral_clusterVol_cutoff_Iio` therefore assume finiteness
of the mean **at the endpoint parameter** and only then compose the limit with
`ENNReal.tendsto_toReal`.

Thus an unconditional real-valued `hmeet` at criticality is still not claimed.
Where a model gives finite mean at the endpoint, the exact real-valued left
limit is now available.

## Explicit radius bounds and the least admissible threshold

If `F r ≤ χ` and `χ ≠ ⊤`, `eventual_rpow_bound_of_le` proves

```text
(F r).toReal ≤ (2α / β) * r^α
```

eventually in `r`, with an explicit threshold

```text
max 1 ((χ.toReal / (2α/β))^(1/α)).
```

This is elementary scaling, not a proof of `χ ≠ ⊤`. For monotone `F`,
`exists_minimal_eventual_rpow_bound` takes the infimum of admissible thresholds
and proves it is itself admissible and minimal. Continuity of `r ↦ r^α` and
monotonicity are used at that infimum; no invented continuity assumption on
`F` is made.

`cutoff_eventual_rpow_bound_of_uncut_ne_top` and
`cutoff_minimal_sharpness_threshold_of_uncut_ne_top` apply these results to the
cutoff mean. Their sole moment premise is finite uncut mean at the designated
parameter, exactly the input that remains open near criticality. Terminal
finiteness is not inferred from zero percolation probability.

Finally, `exists_uniform_cutoff_bound_iff_uncut_ne_top` identifies a finite
uniform-in-radius mean bound with finite uncut mean. Both directions are
proved from cutoff monotonicity and convergence; neither side is asserted.

## Relation to other work

`PowerLawHighTemp` supplies finite uncut means in the explicit small-parameter
regime `β M < 1`, not throughout the subcritical interval. Accordingly, these
bootstrap ingredients do not become the complete Lemma I.4.9. The ODE,
differentiability and logarithmic-error obligations are untouched. The
finite-volume Russo identity already exists elsewhere; it was deliberately not
duplicated. Gap B's uncapped derivative and its termwise continuity,
window-flux measurability and endpoint mean conditions remain separate work.

The candidate came from Ultramath member m1. The integrator reviewed its
actual `ℝ≥0∞` versus real-valued statements and added the explicit
finite-endpoint `toReal` wrappers. Focused compilation and axiom reports are
local evidence, not upstream CI or an assertion of source completion.

## A framework counterexample, not a source-model counterexample

`CriticalLRP/RayRefutation.lean`, checked from swarm `smwpgngy4`, contains an explicit
non-translation-invariant ray whose edge intensities are
`J s(i,i+1) = log (i+2)` and zero otherwise. At `β = 1` it proves
`infiniteClusterProb = 0`, while the expected cluster cardinality at the origin
is `⊤`. `ray_expectedDegree_le_two` gives a uniform expected-degree bound of
`2` at each vertex. At `β = 2` the ray percolates, proving only `β_c ≥ 1`:
no equality `β_c = 1` is established, and no strict `β < β_c` counterexample is
constructed.

Thus absence of an infinite cluster, even together with bounded expected
degree, does not imply finite mean without model structure. The paper's
translation-invariant power-law model and genuine sharpness are essential and
are not provided by this counterexample. Its growing intensities also show the
separate role of uniform ellipticity.

For comparison, `le_criticalBeta_of_forall_lintegral_ne_top` proves that finite
mean at every vertex puts the parameter below `β_c`, given a nonempty
percolating set. That is the valid inclusion; it is not a proof of subcritical
mean finiteness. Nor can the existing analytic corollaries close the gap:
`tendsto_cutoffMean_nhds_top_iff_uncut_eq_top` identifies the critical
infinite-mean premise itself, modulo the stated kernel hypotheses.

## A second counterexample: no percolation, yet infinite means at all positive parameters

`CriticalLRP/BushRefute.lean` constructs a root with hubs `n`, where each hub
has a finite bush of leaves. The fan edge has weight `2⁻ⁿ` and each hub-leaf
edge has weight `1`. Borel–Cantelli makes only finitely many fan edges open
almost surely, so all clusters are finite and even
`criticalBetaSet kernel kernel_nonneg = ∅`.

`BushRefute.sum_leaf_le_tsum` embeds a bush into the global `tsum` of
connection probabilities. A two-edge cylinder bound and the row-size estimate
then give `lintegral_clusterVol_root_eq_top` at every `β > 0`, not an unproved
counterexample from a report. The extra embedding and public export were
independently checked during integration.

`rows_unbounded` proves that this model violates the uniform row-sum
hypothesis, so it does not contradict `PowerLawHighTemp`. It is a framework
counterexample, not a finite-window example or a counterexample to the
paper's stationary lattice. Together with the ray, it keeps the remaining
source-critical obligation explicit: model structure and genuine sharpness
cannot be replaced by an appeal to absence of infinite clusters.
