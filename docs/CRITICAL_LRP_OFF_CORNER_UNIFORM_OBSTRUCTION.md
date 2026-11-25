# Off-corner `stdDegree`: uniform majorants and an obstruction

Integrated from the accepted negative result `smwudd7jf/m2` in
`Analysis/Cutoff/OffCorner/UniformObstruction.lean`. This is a precise obstruction to a proposed
uniform majorant, not a refutation of the off-corner flux itself or of any moment identity.

The coefficient is

`stdDegree r = #(ball r) * (-deriv K r) / gapFloor r`.

An attained source radius `s` supplies a candidate kernel gap. Past the tail threshold,
`gapFloor_le_gap_to_attained` gives `gapFloor r ≤ K s - K r` for `s < r`, and tail strict decrease
makes it an admissible positive gap. By the mean value theorem, that gap is bounded by a
derivative constant times `r - s`. On the other hand, the source's tail lower derivative bound
keeps `-K'(r)` positive. For `r` just above an attained `s`, `le_stdDegree_of_window` therefore
proves a lower bound of the form

`(1/4) (s / (s + e))^(d + α + 1) / (r - s) ≤ stdDegree r`

once the factors are combined. Since the standard ball contains the origin, the cardinality
factor is at least one.

## Consequences are proved directly in Lean

* `exists_stdDegree_gt`: every real constant is exceeded on each right-window of an attained
  tail radius;
* `not_bddAbove_stdDegree_Ioo`: `stdDegree` is unbounded on every open compact window containing
  an attained tail radius, even after excluding the off-corner set;
* `exists_attainedRadii_gt`: attained radii are unbounded above, using scalar multiples of
  nonzero lattice points;
* `not_bddAbove_of_stdDegree_le`: no pointwise majorant of `stdDegree` can be bounded on these
  compact windows either;
* `not_eventually_le_const_mul_rpow`: the proposed `C r^(-d-α-1)` tail bound is false.

The lower bound makes the obstruction structural: division by another edge's vanishing gap
standardizes against the wrong local scale. It does not imply that the cutoff derivative weight
itself blows up, nor does it invalidate the fixed-radius flux estimate.

## Separated-radius alternative

The positive alternative `gapFloor_ge_of_separated` and `stdDegree_le_of_separated` gives an
explicit bound when the radius stays at least `ε` above every attained radius below it. The
constant retains the tail interval's endpoint, derivative constants, and `min ε (a - R)`. This is
an exact separated-radii condition, not an invented positive lower source gap. Fixed-radius or
un-standardised estimates are the other available routes.

**Not claimed:** no non-integrability statement. `IntegrableOn stdDegree (Ioi r₀)` remains
undecided here. An integrable function may be unbounded on infinitely many windows, and this file
does not formalize either the required reciprocal integral computation or the relevant
lintegral comparison. It also does not assert absent measurability. The result rules out bounded
compact majorants and the proposed power-law majorant, nothing more.

All 13 declaration audits use only `propext`, `Classical.choice`, and `Quot.sound`.
