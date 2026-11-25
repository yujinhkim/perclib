# Locally finite corner radii at arbitrary normalized norms

`Analysis/Cutoff/CornerRadii/Defs.lean` defines attained radii of nonzero
lattice vectors at a `SourceNormData`, and proves their identification with the
pairwise `cornerRadii` used by `Analysis/Cutoff/IntervalAC`.
`Analysis/Cutoff/CornerRadii.lean` proves local finiteness and counting.
`CornerRadii/FlatSharpness.lean` checks optimality at the flat norm.

The attained radii below a bound are the image of nonzero vectors in an
already-finite normalized lattice ball. Hence every bounded interval contains
only finitely many corner radii, with cardinality at most that of its containing
ball. The landed ball-ratio error gives polynomial upper bounds in the upper
endpoint, a two-scale window bound, and an `O(b^d)` estimate.

The package also supplies an explicit finite `Finset` of corners, closedness,
isolation of every attained radius, corner-free neighbourhoods of other radii,
existence of off-corner points in every nondegenerate interval, and
Lebesgue-nullness in each bounded window.

The flat norm has a shortest attained radius `1/2` and every positive
half-integer as an attained radius, so its global corner set is infinite.
Nothing assumes distance at least one or global finiteness. Finiteness is local
in the interval only.

No continuity or derivative of the cut mass follows from geometry alone. The
new result supplies the finite-corner-set premise of `IntervalAC`; the actual
derivative and continuity premises remain separate obligations.
