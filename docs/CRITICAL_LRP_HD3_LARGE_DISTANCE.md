# Literal and large-distance HD(3)

`Analysis/SecondMomentCase3/TriangleFromHD/LargeDistance` records the
`smwznoz6j` member-m1 audit at production base
`bd25afb1130f7fe93446b447f9a68a4d3aba08cc`.

## What the literal formal hypothesis entails

Lean's `(Real.log 1)⁻¹ = 0`. Consequently the literal `Case3HD` implies every
nonzero normalized lattice distance is at least `1`, and forces two-point
probability zero at distance exactly `1`. A distance in `(0,1)` makes the
stated right-hand side negative even though a probability is nonnegative.

`FlatSix` constructs a source norm at `d=6` whose unit ball has Lebesgue volume
one and whose first basis vector has norm `1/2`. `withNorm` preserves the
source-normalized power-law kernel structure, giving a genuine
`SourceModelData` at `d=6`, `α=2` on which `not_case3HD_flatModel6` holds.
The hypothesis therefore does not follow from the paper's unit-ball-volume
normalization alone. This is a statement about the formal model class, not an
error in the paper: HD(3) is an explicit assumption and may be false on such a
flattened model.

## The restrained hypothesis actually consumed

`Case3HDPos` asks for the log-corrected two-point upper bound only at distance
greater than `1`. `Case3HDLarge` asks for it only at distance greater than `4`,
where the earlier convolution proof actually used it. Both follow from literal
`Case3HD`. With the short-distance conditions made explicit, the positive-log
form is equivalent to the literal one.

`case3HDLarge_iff_Wt_majorant` identifies `Case3HDLarge` exactly with the
positive-log majorant used by (I.4.12). This avoids an artificial near-origin
sign condition but does not prove the estimate. The remaining probabilistic
input is the distance-restricted two-point estimate expected from the source's
lace expansion, not a triangle, tail, or moment bound inferred from a desired
conclusion.

`Main.lean` proves the majorant implication in both directions, and `Bridge.lean`
re-runs the two convolution stages and all four Case-3 source wrappers from
this large-distance input. Finite triangle, the logarithmic tail and the
logarithmic-error function use the same normalized-norm and summability gates
as the original package. Every other ODE, moment, measurability,
log-integrability and moment-gap hypothesis of those wrappers is unchanged.

There is no nontrivial critical HD(3) instantiation in this package. In
particular, the numerical remark about a Euclidean-like unit-volume norm is not
used as a formal model theorem, and the large-distance lace bound itself stays
open. No uncut critical tail, `HasCovBound`, or I.4.20 asymptotic follows.

The candidate and its 30+9 audits were independently rebuilt with strict flags;
all exports use only `propext`, `Classical.choice` and `Quot.sound`. The
integrated `LargeDistance.AuditBridge` target builds with `--wfail`.
