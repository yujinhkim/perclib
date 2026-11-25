# Finite-volume Russo formulas at arbitrary norms

`Analysis/Cutoff/FiniteRusso/Defs.lean` defines affine edge-parameter paths,
normalized-norm cutoff profiles, finite cluster moments, and the two binomial
weights. `ModelDefs.lean` contains the actual `SourceModelData` wrappers.

The other modules prove exact one-edge increments, an integrated Russo
identity along the affine parameter path, interval increments with the boundary
convention `len(e) < r₂`, exponential-weight majorants, monotonicity, and an
off-corner derivative with binomial weights. `AnchorSum` performs the literal
finite sum over anchors. `LowerEndpoint` gives the normalization at the lower
cutoff boundary, and `OffCorner` avoids edge-length radii explicitly.

These are finite-configuration, finite-volume results. They are not the
infinite cutoff-mass ODE, do not by themselves permit infinite-volume Russo
differentiation, and do not allow corner two-sided derivatives. The subsequent
`Fibre/RussoAssembly` package connects the standardized excluded increments
and cofinal-window limits to the actual infinite product law; see
`CRITICAL_LRP_RUSSO_EXCLUDED_ASSEMBLY.md`. Complete differentiation still
requires explicit summability, dominating-moment and local-continuity inputs.
