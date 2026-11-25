# Conditional off-corner Russo derivative in excluded-mass form

Integrated from the accepted `smwudd7jf/m1` packet in
`Analysis/Cutoff/RussoExcluded/{Defs,Main}.lean`. The related bounded-majorant obstruction is in
`CRITICAL_LRP_OFF_CORNER_UNIFORM_OBSTRUCTION.md`; it is not used to replace this result's explicit
inputs.

`pairFlux M r y e` is the actual derivative weight on edge `e` times the singleton-cluster
pivotal flux at `y`. `pivotalFlux_sMomentTrunc_eq_sum_singleton` expands a finite truncated
cluster moment into singleton fluxes. The singleton flip difference is an indicator difference,
bounded and measurable, so the finite additivity is an ordinary finite-integral argument with no
uncapped moment premise.

This yields the exact finite identity
`sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairFlux`: the standardized edge-window sum equals the
sum of `pairFlux` over the corresponding finite vertex-edge rectangle. In particular, the
vertex-series and excluded-flux expressions are two orders of summing one family, not two merely
similar quantities.

`tendsto_codeWindow_product` proves that the canonical square windows are cofinal in finite
subsets of `M.V × Sym2 M.V`. Under absolute summability of the pair family,
`tendsto_sum_rect_pairFlux` sends their sums to the full product `tsum`. Comparing those limits
with the already established D1C limit proves

`tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass`:
the summed vertex flux is
`β_c * (-deriv K r) * (E1Sign.exclMass r).toReal`,
provided `exclMass r ≠ ⊤` and the pair family is absolutely summable.

`hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass` substitutes this value into the existing
`hasDerivAt_cutMassReal_tsum_sMomentInfFlux`. It retains all of that theorem's hypotheses: the
exhaustions, corner-free local window, derivative and summability conditions, moment/measurability
input, continuity, finite cutoff mass, per-vertex integrability and summed-flux continuity. The
additional inputs are exactly finite excluded mass and pair summability.

The nonnegative singleton fluxes obtain several sharper reductions without assuming needless
uniformity:

* `le_tsum_sMomentInfFlux_betaCrit_mul_exclMass` gives the excluded-mass value as a lower bound
  on the summed flux, with per-`y` edge summability, vertex summability and finite `exclMass`;
* `summable_abs_pairFlux_of_nonneg` derives the required absolute pair summability from those
  two summability hypotheses, using nonnegativity;
* `tsum_eq_iff_le_betaCrit_mul_exclMass` reduces equality to the missing reverse domination of
  the summed flux;
* `hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_nonneg` proves the same actual off-corner
  derivative using per-`y` edge summability instead of assuming pair summability separately.

**Summability continuation.** `OffCorner/PairFluxSummable` now proves the per-`y` edge
summability from a finite mixed first moment at a fixed off-corner radius; an ordinary first
cutoff moment suffices. Consequently the derivative variant `..._of_cutMass` removes `hinner`.
The `y`-series, finite `exclMass`, and other regularity inputs remain. See
`CRITICAL_LRP_PAIR_FLUX_SUMMABLE.md`.

**Remaining inputs and limitations.** The `y`-series summability and finite excluded mass are not
free, and this does not prove a radius-uniform majorant. Earlier analysis of the paired residual
remains relevant when assessing the source-model input: a fixed edge contributes an average
cluster-volume difference at the critical cutoff. The `hdom` edge-majorant itself does not establish
the separate `y`-series. The `RussoExcluded` wrapper does not prove a radius-uniform majorant,
local absolute continuity, an ODE, corner identities, finite large-radius moments, or Lemma I.4.1
unconditionally. Infinite `exclMass` is never converted to real zero.

All 16 declaration audits use only `propext`, `Classical.choice`, and `Quot.sound`.
