# Two-point and normalized-pivotal radius continuity

Accepted from Ultramath `smwv2c2lw`, member `m2`. Production modules:
`Analysis/Cutoff/OffCorner/TwoPoint/`.

Let `r₀ > 0` and `r₁ > r₀`, with `M.cutMassAt r₁ 0 ≠ ⊤`. Then the cutoff two-point function is
continuous at `r₀`: `continuousAt_cutLaw_conn` and `continuousAt_cutTwoPoint`. The same is true
for single-edge forced connection probabilities and fixed-edge singleton pivotal flux.
`continuousAt_normalizedPivotMass` supplies the corresponding normalized aggregate continuity
when additionally `r₀` is off the attained-radius set. Second-cutoff-moment variants are included.

The ordinary connection event is split into a finite-box connection plus a genuine infinite-volume
escape event, not approximated by a finite box with an unproved limit step. The finite-box part is
controlled quantitatively: differing thresholded configurations on a finite edge set change any
event probability by at most the total variation of the edge parameters on that set. Continuity
of the individual cutoff profiles makes this variation vanish locally. A fixed integrable cluster
makes the escape probability vanish as the ball grows, and monotonicity gives a usable bound over
the relevant radius window. The resulting estimate is exactly finite-range variation plus two
escape terms, in both directions.

Forcing a single edge leaves its cluster inside the union of the ordinary clusters of its two
endpoints and the original root. A finite number of ordinary escape bounds therefore also controls
the forced escape event. Forced-box configurations remain finite-determined, so the same variation
argument applies. Subtracting the forced-open and forced-closed connection probabilities gives
the unweighted fixed-edge pivotal difference; no monotonicity of that difference in the cutoff
parameter is assumed.

This discharges the fixed-edge hypothesis of the separately proved aggregate majorant. The bundle

* `edgeTouchMass` and `pivotMajorant`;
* locally frozen normalized factors off attained radii;
* the first-moment incident bound;
* `continuousAt_pivotalFlux_singleton` from this packet;

then yields normalized-pivotal continuity through the full infinite edge series, not only a
truncated sum. The main capstone is available in the first- and second-cutoff-moment forms.

These results do **not** provide the finite first (or higher) moment at arbitrary large radius,
prove `β_c ≠ 0`, prove excluded-mass continuity from these hypotheses alone, establish a cutoff
ODE, or assert the paper's principal theorems. At the application boundaries, the off-corner and
explicit moment inputs remain visible. The two-point/forced-edge proofs themselves do not exclude
attained radii; cutoff profile continuity covers them, while the aggregate still requires its
geometric off-corner condition.

All ten modules were rebuilt independently in dependency order with strict flags, and again after
moving their local imports to production paths. At that stage `TwoPoint.lean` was separately
found missing from the barrel and was added explicitly, so all 831 modules—not just the ten
production files—are covered by the check. The root build exposed duplicate helper names introduced by the packet. Integration deleted only
those helpers and reused the existing `one_le_clusterVol` and `cutMoment_one_ne_top_of_two`
lemmas, with no change to the main theorems or their hypotheses.

Audited declarations use only the standard axioms.
