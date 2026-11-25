# Integrated cutoff-flux interchange without a radius-uniform vertex majorant

`Analysis/Cutoff/IntegralFluxInterchange.lean`, accepted from swarm `smwtvrwnn` member `m4`, provides an alternative to `hasDerivAt_cutMassReal_of_summableMajorant` by integrating in the radius before taking the vertex limit.

## Results and exact scope

- `lintegral_iSup_ofReal_eq_ofReal_of_tendsto_intervalIntegral` is the underlying monotone-convergence theorem for interval integrals.
- `lintegral_tsum_sMomentInfFlux_eq_ofReal_sub` identifies the extended nonnegative integral of the whole vertex series of one-sided-free, off-corner two-point fluxes with the cutoff-mass increment over `Ioc a b`. On a corner-free open window it retains the existing two-point derivative hypotheses, finite first cutoff mass on `uIcc a b`, per-vertex interval integrability, and per-vertex flux nonnegativity. It assumes no `y`-summability and no radius-uniform per-vertex majorant.
- `intervalIntegral_tsum_sMomentInfFlux_eq_sub` is the real-valued integrated identity. It additionally requires `0 < a` and summability of the flux series in `y` at each radius of `Ioc a b`, but no uniformity in the radius.
- `hasDerivAt_cutMassReal_tsum_sMomentInfFlux` gives the actual off-corner pointwise derivative of `cutMassReal` as the summed flux. Besides the previous regularity, finite-moment, nonnegativity, pointwise-summability, and per-vertex-integrability inputs, it assumes continuity of the summed flux throughout the corner-free window.
- `abs_sMomentInfFlux_le` gives the pointwise-in-radius domination of one vertex's flux by its total pivotal weight and can turn the existing pivotal-weight integrability into per-vertex flux integrability under the appropriate measurability input.

The proof removes `u`, `Summable u`, and the uniform-in-radius bound `|flux_y(r)| ≤ u(y)`. It does not derive the replacement summability or summed-flux-continuity hypotheses, the existing two-point regularity inputs, large-radius finite moments, the standardized edge-flux factorization, or any statement at a cutoff corner. It is an alternate conditional interchange theorem, not an unconditional infinite-volume Russo formula and not a completion of Lemma I.4.1.

`RussoExcluded` now additionally identifies the two summation orders. Under finite `exclMass`
and absolute pair summability it gives the summed flux as
`β_c(-K') exclMass.toReal`; in the nonnegative case this summability follows from per-`y` edge
summability and the already assumed vertex summability. The remaining hypotheses, including
nonnegativity and summed-flux continuity, are still required. See
`CRITICAL_LRP_RUSSO_EXCLUDED_DERIVATIVE.md`.

`RussoExcluded` itself also retains a more explicit pair-summability variant. The subsequent
`OffCorner/PairFluxSummable` and `OffCorner/EdgeMajorant` wrappers derive the per-`y`, vertex and
`hdom` inputs from finite first/second cutoff moments at fixed radii. With finite
`cutMoment 2 r` on the local corner-free window,
`hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMoment_two` retains only the remaining
regularity, measurability, interval-integrability and continuity inputs. No large-radius moment
or ODE follows.

The recovered `OffCorner/RadiusMeasurability` package now also provides `hmeasK` by monotonicity
of edge-event probabilities and `hmeasinf` from finite first cutoff mass, and explicitly keeps the
jump at attained edge lengths distinct from continuity. `OffCorner/RadiusEnvelope` supplies a
summable radius-independent edge envelope on interior windows subject to nonvanishing `K'(ρ)`.
See `CRITICAL_LRP_RADIUS_MEASURABILITY.md` and `CRITICAL_LRP_RADIUS_ENVELOPE.md`.
These reduce the endpoint wrapper's remaining inputs to `hboundint`, `hcontinf`, and `hGcont`;
they do not complete those remaining arguments.
