# Monotonicity of the mixed cutoff density

`Analysis/Cutoff/MixedFluxDensityMonotone.lean`, accepted from swarm `smwtzmkep` member `m3`, proves that `mixedFluxDensity r y = E_r[|K_0| 1{y∈K_0}]` is monotone in the cutoff radius at positive radii.

The proof writes the mixed density as the `tsum` of joint cluster probabilities `{x∈K_0}∩{y∈K_0}`. Those events are increasing and measurable, so `edgeMeasure_mono_of_le` applies termwise. `cutLaw_mono_apply` provides the actual cutoff version, and `ENNReal.toReal_mono` converts the comparison with only a finite first moment at the larger radius. `cutMoment_one_le_two` and `cutMoment_one_ne_top_of_two` give the commonly used second-moment variant, while `mixedFluxDensity_le_cutMoment_two` bounds the density by the full quadratic moment.

`mixedFlux_le_mixedFluxDensity_right` and `mixedFlux_le_mul_mixedFluxDensity_right` lift per-radius bounds to a uniform majorant at a fixed right endpoint. `exists_summable_perY_fluxMajorant_of_perRadius` discharges the earlier majorant input from such a per-radius bound and finite second moment. The per-radius flux bound itself (`hloc`) remains explicitly unproved here; it is the incident transport task assigned to a separate direction.

`hasDerivAt_cutMassReal_of_perRadiusBound` retains every prior corner, differentiability, domination, integrability, measurability, continuity, finite-mass, and local-bound hypothesis. It is a reduction of the local majorant premise, not a new unconditional derivative. The zero radius is excluded exactly where required by cutoff-profile monotonicity, and no critical infinite moment or model completion is claimed.
