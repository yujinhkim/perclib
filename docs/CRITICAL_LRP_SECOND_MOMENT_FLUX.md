# Finite-second-moment off-corner flux inputs

`OffCorner/SecondMomentFlux.lean` completes the fixed-radius second-moment reduction that the
exhausted exploration `smwueko56` did not return. The coordinator checked the short wrapper
independently; it introduces no untried analytic route.

`E1Sign.exclMass_ne_top_of_cutMoment_two` gives finite excluded mass from `cutMoment 2 r ≠ ⊤`.
`mixed_ne_top_of_cutMoment_two` gives finiteness of every mixed first mass by integrating the
cluster-volume bound. The old resampling identity supplies summability of the mixed density,
whose value is controlled by the same second moment, and the established off-corner
`abs_sMomentInfFlux_le_stdDegree_mixed` is only used at this fixed radius.

Thus `summable_sMomentInfFlux_of_cutMoment_two` proves the vertex-series summability originally
taken as `hsumm` (and its absolute counterpart). `summable_pairFlux_of_cutMoment_two` gives the
per-`y` edge series through the first-moment consequence of the second. The equality
`tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass_of_cutMoment_two` assembles these inputs with the
D1C value: the summed vertex flux is `β_c (-deriv K r) exclMass.toReal`.

**Exact scope:** `0 < r`, `r ∉ attainedRadii`, and finite second cutoff moment at that radius.
These theorems discharge several summability obligations without any uniform-in-radius
`stdDegree` bound. They do not prove the moment exists for a large radius, supply continuity or
absolute continuity, prove a complete derivative/ODE, or address attained radii. The remaining
local `IntegralFluxInterchange` hypotheses are unchanged.

The subsequent `OffCorner/EdgeMajorant` derives `hdom` from a finite first cutoff moment using
the unstandardized normalized-ball degree. Its final wrapper derives the derivative value under
a finite second cutoff moment on the local window, while retaining the other regularity and
continuity inputs explicitly. See `CRITICAL_LRP_OFF_CORNER_EDGE_MAJORANT.md`.

`OffCorner/ScalarFactor` additionally weakens the required second cutoff moment to its value at
the outer endpoint, supplies a scalar outer-factor bound, and derives nonnegativity,
measurability-at-filter and per-vertex interval-integrability from per-vertex continuity.
See `CRITICAL_LRP_OFF_CORNER_SCALAR_FACTOR.md`.

All seven declarations were checked with the strict project flags and depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
