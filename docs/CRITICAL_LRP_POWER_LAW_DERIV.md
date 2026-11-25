# Derivative regularity of the explicit power-law model

Accepted from Ultramath `smwv2c2lw`, member `m4`. Production module:
`Analysis/Cutoff/OffCorner/PowerLawDeriv.lean`.

The repository's `Witness.sourceModelWitness` uses the normalized sup norm `2‖·‖∞`, whose unit
ball has volume one, and `K(r) = r^{-d-α}/(d+α)`, for `d ≥ 1` and `α > 0`. Thus `K(r)` has the
paper's exact derivative convention, `|K'(r)| = r^{-d-α-1}` (zero logarithmic error), and is not a
vacuously abstract `SourceModelData` instance.

The new analytic core proves `K'(r) = -r^{-d-α-1}`, continuity of `deriv K` on `Ioi 0`, strict
negativity and its absolute-value form. `sourceModelWitness_hK`, `_hKd`, `_hCb`, and `_hKβ`
supply the off-corner wrappers' kernel-side inputs at this model. It does not derive continuity
of `deriv K` for an arbitrary `SourceModelData`, where `K_diff` is only differentiability.

The endpoint instantiations delete those kernel-side premises and identify explicitly
`rhsScalar r = β_c r^{-d-α-1} (exclMass r).toReal`. They still require the off-corner window,
finite endpoint second moment and the appropriate per-vertex continuity (`hcontinf` or normalized
`hB`), and excluded-mass continuity or the cylinder approximation. Nonzero `β_c` remains a
hypothesis wherever the scalar equivalence needs it. The left strict-weight envelope is also
specialized to every positive radius, retaining the finite first moment there.

No large-radius moment, explicit `β_c ≠ 0`, per-vertex/pivotal/excluded-mass continuity or ODE is
asserted. The power-law derivatives are elementary real analysis, not a new probabilistic proof.
The locally assembled `_of_endpoint_of_moments` and `_powerLaw_of_moments` variants retain the
finite second/third cutoff moments at the right endpoint and `hcontinf`, while deleting the
excluded-mass continuity premise using `RadiusExcludedMass`. They express the derivative in both
`rhsScalar` and explicit power-law form. Both declarations were rebuilt in the production module
and have only the standard axioms.

The file's targeted axiom block covers a subset of its declarations; the full production audit
covers all of them.
