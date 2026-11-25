# Per-vertex edge summability of the off-corner pair flux

Integrated from the accepted `smwue873v/m1` packet in
`Analysis/Cutoff/OffCorner/PairFluxSummable.lean`.

`summable_pairFlux` proves, at `r > 0`, `r ∉ attainedRadii`, and a finite mixed first moment
`E_r[|K_0| 1{y ∈ K_0}]`, that `e ↦ pairFlux M r y e` is summable. It also gives the absolute
version and the quantitative bound

`∑'_e |pairFlux r y e| ≤ stdDegree r * mixedFluxDensity r y`.

The termwise bound is `|pairFlux| ≤ stdEdgeWeight(e) * P_r({y ∈ K_0} ∩ {e touches K_0})`.
The finite-degree input is the already established fixed-radius bound `stdDegree r`; it requires
no uniformity in the radius. The mixed incident transport makes the series of standardised
weights summable from finite mixed mass. Pair flux is then dominated term by absolute value.
This uses genuine constructed summability, not just a `tsum` bound.

`lintegral_mixed_le_cutMoment` bounds the mixed mass by the ordinary first cutoff moment, so
`summable_pairFlux_of_cutMoment_ne_top` and `summable_pairFlux_of_cutMassAt_ne_top` provide the
corresponding ordinary-first-moment variants. These are conditional per-radius theorems, not
moment existence results.

The comparison wrappers `..._of_finite_mixed` derive the previously explicit per-`y` edge
summability from the finite mixed moment. Crucially,
`hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMass` **deletes** the nonnegative
conditional derivative's separate `hinner` input: finiteness of `cutMassAt` on its local window,
positivity and off-cornerness already imply it at the target radius. The `y`-series summability,
finite `exclMass`, and all existing regularity, integrability, and summed-flux-continuity inputs
remain visible. This is not an unconditional derivative theorem.

Going the other way, the bound has an ℓ¹ constant depending on `stdDegree` and the mixed density,
so it does not establish `y`-summability without an independent second-moment input. At attained
radii the standardised weight degenerates by the Lean `0/0 = 0` convention, so this route is
silent there. `UniformObstruction` remains the relevant reason that no bounded majorant can be
assumed uniformly in `r`.

The subsequent `OffCorner/SecondMomentFlux` additionally discharges the vertex-series
summability and finite-`exclMass` premises at a fixed radius under a finite second cutoff moment.
Its sum equality uses the same second-moment input throughout; see
`CRITICAL_LRP_SECOND_MOMENT_FLUX.md`. This still does not prove moment existence or the remaining
local absolute-continuity hypotheses.

All 12 theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`.
