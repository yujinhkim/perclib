# High-temperature susceptibility for the power-law lattice

`CriticalLRP/PowerLawHighTemp.lean` proves a finite-susceptibility interval for
the canonical independent-edge power-law model on `ℤ^d`, using only the
row-sum/branching bound. It does **not** prove sharpness at the critical
threshold.

## Exact model and explicit interval

Let `d ≥ 1`, `s > d`, and write

```text
M = ∑' z : ℤ^d, ‖z‖∞^(-s).
```

Here `0^(-s) = 0` since `s > 0`, so the diagonal term vanishes. The existing
`LatticeGeometry.summable_linfNorm_rpow` proves that this mass is finite. For a
pair intensity `J(x,y) = ‖y-x‖∞^(-s)` (with the `ℝ≥0`/`Real.toNNReal` coercions
explicit in Lean), all off-diagonal rows are bounded by the corresponding
nonnegative real `M.toNNReal`.

`power_chi_intensity_le` gives, for every vertex `x`,
`χ(x) ≤ (1 - β M)⁻¹` whenever `β M < 1` in `ℝ≥0∞`. Consequently,
`power_chi_intensity_lt_top` and
`power_kernelJ_lintegral_clusterVol_ne_top` prove a genuinely finite expected
cluster volume. `power_kernelJ_infiniteClusterProb_eq_zero` independently gives
zero probability for the event that some cluster is infinite; it is not used in
reverse to infer finite mean.

The interval is nonempty: `exists_beta_interval_power_kernelJ_chi_lt_top` takes
`β₀ = (M+1)⁻¹`, which is positive, and proves finite mean for every `β < β₀`.
Both `power_globalCriticalIntensity_pos` and
`power_rootCriticalIntensity_pos` conclude that the critical intensity is
positive. No assertion that the threshold equals `M⁻¹` is made.

## Compatibility with the cutoff dominance interface

`power_uncutFirstMoment_ne_top` supplies the exact uncut
`kernelJ`/`longRangeMeasure` first-moment premise used by `CutoffDominated`.
For the paper's radial profile with `α > 0`, set `s = d + α` in
`modelProfile_uncutFirstMoment_ne_top`. The radial norm here is the
existing `linfNorm`, and the profile is `r^{-(d+α)}` with its zero-at-zero loop
convention.

`chi_lt_top_of_le_powerLaw` transfers finite mean to every smaller pair
intensity `J_r ≤ J` in the same explicit interval. Edge profiles, pairwise
open probabilities and the native `law` are not silently identified: proof
irrelevance lemmas handle the different nonnegativity and evenness arguments.

This supplies the cutoff dominance input only when the **reduced parameter** is
in its explicit high-temperature interval. Choosing `β₀` so that `β₀ M < 1`
allows `lintegral_clusterVol_cutoff_ne_top_of_subcritical` to be instantiated
there, with the monotonicity of the uncut mean supplying smaller parameters.

## What remains open

The dominance needed by the paper uses a reduced parameter `β_c(1−ε)` near
`β_c`. Nothing here proves that this parameter is smaller than `1/M`, nor does
it give finite mean on the whole interval `β < β_c`. The dominance construction
therefore does not yet become the source sharpness theorem. No inference from
`infiniteClusterProb = 0` to finite mean is used; the existing binary-tree
counterexample explains why that shortcut is false.

This result does not change GAP B: capped versus uncapped cutoff derivatives,
`hcontterm`, `hmeas` and the endpoint finite-mean inputs of
`CutoffFluxMajorant` remain untouched. The new finite-mean interval also does
not complete I.4.9 or supply triangle finiteness at criticality.

## Scope and provenance

The module adds theorems and compiled witnesses, not new mathematical
structures or definitions. All its probability statements use the existing
native `Config`, `clusterVol`, bond law and `longRangeMeasure`. Its only analytic
summability input is the already formalized `LatticeGeometry` theorem. The
candidate was supplied by Ultramath member m4 and rebuilt after conversion to
public-module form by the integrator.

## Generic exponential and all-order BFS moment bounds

Accepted submission `smwpdapl6`, integrated under
`CriticalLRP/Exploration/BFS/HighTemperature/`, proves a separate
infinite-volume theorem for **any** countable vertex type and any actual
independent Bernoulli edge law `prodBernoulli p`. Let `UniformRowBound p m` mean
that every finite off-diagonal partial row sum is at most the real number `m`.
No transitivity, local-finiteness, finite-range or finite-window assumption is
used; almost-sure local finiteness is proved at each finite BFS horizon.

The remaining-generation induction `gen_moment_induction` applies to every
`IsHistFun` history function, not just the root. At the root, horizon and
monotone-limit arguments give, for `0 < m ≤ 1`, `1 ≤ λ`, and
`m λ ≤ exp (m-1)`,

`∫⁻ ω, epow (ofReal λ) ((cluster ω o).encard) ≤ ofReal (1/m)`.

This is `lintegral_epow_encard_cluster_le_inv_mul`. The `m=0` endpoint has the
separate bound `ofReal λ`. BFS refinement means no first-hit independence or
independence of overlapping branches is assumed.

For every natural `k`, `lintegral_pow_encard_cluster_le_inv_mul` bounds
`∫⁻ ofReal (((cluster ω o).encard.toNat : ℝ)^k)` by
`ofReal ((1/m) * (k!/(log λ)^k))` when `λ > 1`.
`exists_lam_lintegral_epow_encard_cluster_le` and
`exists_lam_lintegral_pow_encard_cluster_le` produce an admissible `λ > 1` for
`0 < m < 1`. Almost-sure cluster finiteness is derived from the extended
exponential bound before using `toNat`; it is never a premise hidden in the
moment statement. Variants are supplied for the diagonal-inclusive `RowSum`.

No statement at `β_c` or about the source model's cutoff moments follows.
In particular, the generic all-order fact does not close
`hutchcroft.i.1.5.step.cutoffmoments`.

## Power-law all-moment application

`CriticalLRP/IntensityMoments.lean` connects the existing intensity-row bound
to the generic BFS theorem. `uniformRowBound_intensityProfile` preserves the
real finite-partial-row interface; it does not introduce another probability
measure. `exists_lam_envelope_intensityProfile` handles an empty row budget as
well as a positive one, with the same small-`β` interval.

The resulting `power_lintegral_clusterVol_pow_ne_top` takes the **same** pair
profile `J` on `Fin d → ℤ` and condition `β M < 1` described above and proves,
for every root `x` and every natural `k`,

`∫⁻ ω, (clusterVol ω x)^k ∂(law (intensityProfile J β)) ≠ ⊤`.

The proof derives almost-sure cluster finiteness from the extended exponential
bound and then identifies the natural-power cluster-volume integrand on that
event. It therefore does not hide infinite clusters by replacing their
cardinality with zero. This upgrades the previously proved first-moment
interval to all natural moments at the genuine infinite-lattice model.
It remains a high-temperature condition `β M < 1`: nothing is asserted at
`β_c`, about `SourceModelData.cutMoment`, or about the main paper roots.

## Exponential decay of the cluster-volume tail

`CriticalLRP/HighTemperatureTail.lean` applies Markov at `λ^n` to the extended
exponential moment. For a real uniform row bound `UniformRowBound p m`, with
`0 < m ≤ 1`, `1 < λ`, and `mλ ≤ exp(m-1)`, its
`measure_cluster_encard_ge_le_inv_mul_rpow` proves

`P(|K_o| ≥ n) ≤ (1/m) λ^{-n}`

on the actual `prodBernoulli p`. The exponent comparison is exact on `ℕ∞`, and
`le_of_epow_nat_le_of_one_lt` gives the reverse implication needed to identify
`{λ^n ≤ epow λ |K_o|}` with `{n ≤ |K_o|}`. The proof works on the full
configuration space and does not assume a priori that the cluster is finite.
This too is a high-temperature estimate, not a statement at `β_c`.

## Canonical lattice and all-order cutoff statements

`PowerLawHighTemp/Moments.lean` converts the generic theorem to the actual
`lrKernel d α`. `lrKernel_lintegral_clusterVol_pow_ne_top` proves every natural
cluster moment at every vertex under `β M < 1`, and
`exists_beta_interval_lrKernel_clusterVol_pow_ne_top` produces the positive
interval `β < (M + 1)⁻¹`. These are companions to the original first-moment
result, with `k = 1` having the same type. A corresponding form is supplied for
`latticeLongRangeMeasure`.

The same file gives the all-order cutoff statement:
`modelProfile_cutoff_lintegral_clusterVol_pow_ne_top` and its positive-interval
version prove every natural cluster moment at every root for
`cutoffSymKernel (modelProfile d α) d r`, for **every** cut-off radius `r : ℝ`,
under the same condition `β M < 1`. The interval version chooses
`β₀ = (M+1)⁻¹` independently of `r`, so the conclusion is uniform in the radius.
The proof uses `J_r ≤ J` at the same `β` followed by all-order monotone moment
transfer; it does not assume `r ≥ 1`, a reduced parameter, a finite window, or
any sharpness bound.

`law_intensityProfile_eq_longRangeMeasure` supplies the exact probability-law
conversion needed by these statements. All hinge on the high-temperature row
bound. The missing statement at `β < β_c` is not obtained from them.

## Concrete exponential tails of the power-law model

`PowerLawHighTemp/Tail.lean` specializes this inequality to the power-law
intensity, then rewrites its measure to the paper's `lrKernel`.  A positive
high-temperature budget produces `lam > 1` with
`P(|K_x| ≥ n) ≤ (1/m) lam^{-n}` for every natural `n`, where `m` is the real
value of the intensity budget. This is the explicit
`exists_lam_measure_cluster_encard_ge_le_lrKernel` statement, reusing the
verified probability-law identification rather than introducing a new model.
The zero-budget case is segregated from this positive-budget statement; neither
case identifies the threshold or sharpens the full subcritical interval.
