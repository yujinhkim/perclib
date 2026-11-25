# Source-kernel bounds and regular variation

`Analysis/SourceKernelBounds.lean` gives two-sided power bounds on a tail, an
explicit ratio bound with factor `4`, and dyadic shell bounds with geometric
constants. `Analysis/SourceKernelVariation.lean` derives
`K(r) r^{d+α} → 1/(d+α)` and hence regular variation of `K` at index
`-(d+α)`, directly from the `SourceModelData` normalization error and tail
integral.

The residual derivative error is integrated and estimated by dominated
convergence against a summable power, rather than assumed to vanish pointwise
in a stronger norm. No finite-box inference is used.

These are facts about the scalar profile `K`. They are not proved moment,
derivative, or continuity bounds for the actual cutoff cluster mass. The
geometric summation proposed in the member report is not a formalized result;
only the per-scale dyadic estimates are in Lean.
