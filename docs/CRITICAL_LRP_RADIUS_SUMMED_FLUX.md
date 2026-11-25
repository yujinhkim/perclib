# Closed form and regularity of the summed singleton flux

Accepted from Ultramath `smwuinbxz`, member `m1`. Production module:
`Analysis/Cutoff/OffCorner/RadiusSummedFlux.lean`.

At positive off-corner radii with a finite second cutoff moment,
`tsum_sMomentInfFlux_eq_rhsScalar` identifies the infinite vertex sum with the scalar factor
`β_c (-K') (exclMass).toReal`. Finiteness below a finite endpoint and locally finite corner sets
make this identity hold on a neighbourhood of each interior off-corner point. Consequently,
summed-flux continuity is **equivalent** to scalar-factor continuity, not resolved merely by
measurability or boundedness.

The endpoint variants `_of_envelope_of_scalar` and `_of_measurability_of_scalar` instantiate
`hGcont` from continuity of `deriv M.K` and `M.exclScalar` throughout the window. Their envelope
and endpoint moment premises, and per-vertex flux continuity `hcontinf`, remain explicit. This
replaces the summed-flux hypothesis; it does not prove the new scalar hypotheses. Local assembly
also adds `hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail_of_scalar`, applying the same
reduction to the tail derivative wrapper (18 declarations in total, including this assembly).

At a point with `β_c ≠ 0`, continuous nonzero `K'` at the point, and the endpoint moment, the
module also proves equivalence with excluded-mass continuity. `abs_tsum_sMomentInfFlux_le_of_window`
bounds the whole sum, not the separate vertexwise suprema. No summable supremum majorant is
constructed.

Off corner, `ballF_eq_of_offCorner_window` proves that the integration window is locally frozen.
The excluded-mass scalar is then locally a fixed real-valued moment against the varying cutoff
law: `continuousAt_exclScalar_iff_frozenWindow` is an equivalence, and `hGcont_of_frozenWindow`
consumes that frozen-moment continuity. The derivative wrappers also have frozen-window versions.
No continuity of this frozen moment, excluded mass, derivative, or per-vertex flux is established
here. Large-radius moments and a complete ODE remain open. The original module's reported base
was mistaken; the coordinator rebuilt the same file successfully at HEAD `53fa754`.
All 18 declarations use only the standard axioms.

The later `PairMassRegularity` proof supplies the excluded-mass continuity conditionally, from
finite second/third cutoff moments at a larger radius. `RadiusExcludedMass` uses it to derive
`hGcont` on an off-corner window; it still requires continuity of `K'` and `hcontinf`. It does
not close the separate cylinder-approximation formulation by that different route.
