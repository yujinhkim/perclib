# Unstandardized off-corner edge majorants and the derivative wrapper

Integrated in `Analysis/Cutoff/OffCorner/EdgeMajorant.lean`. These results avoid the
`gapFloor` denominator entirely; `UniformObstruction` is not circumvented because it concerns
standardized `stdDegree`, not the unstandardized edge weight used here.

At positive radius, `abs_cutEdgeDeriv_le` gives
`|cutEdgeDeriv r e| ≤ β_c * (-deriv K r)`. The exponential factor is at most one. Every
support edge at a vertex has a source-norm length bounded by `r`, and the number of these edges
is dominated by the actual normalized ball cardinality (`ncard_incidentSupport_le`). Hence
`weight_incident_le` gives the explicit fixed-radius degree bound

`∑ |cutEdgeDeriv r e| * 1{x ∈ e} ≤ β_c (-deriv K r) * #(ball r)`.

No uniform estimate in `r` is claimed or needed.

`summable_weight_touch_of_incident` allows a generic finite incident degree. It applies the
finite absolute incident-mass theorem to derive a **summable** majorant, not merely a final
`tsum` inequality. The factor of two is handled in the actual target family, and the
`Sym2.Mem.decidable` variations are treated by explicit membership case splits rather than
assumed definitional equality. `summable_hdom_of_cutMoment` specializes this to the normalized
ball-count degree and a finite first cutoff moment, thus discharging the local `hdom` of
`hasDerivAt_cutMassReal_tsum_sMomentInfFlux`.

## Second-moment derivative assembly

`hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMoment_two` uses the additional
`OffCorner/SecondMomentFlux` and `OffCorner/PairFluxSummable` wrappers. Under
`M.cutMoment 2 r ≠ ⊤` on the local corner-free window, the following are all derived:

* `hdom`, through finiteness of the first moment;
* `hfin`, finiteness of `cutMassAt`;
* `hsummable`, vertex-series summability;
* the per-`y` edge summability needed within `RussoExcluded`;
* finiteness of `E1Sign.exclMass`.

The resulting actual derivative at `r0` is

`HasDerivAt M.cutMassReal (β_c * (-deriv K r0) * (exclMass r0).toReal) r0`.

The remaining hypotheses are the corner-free open window and differentiability, two exhaustions,
per-vertex weight interval-integrability, window and infinite-flux measurability, per-vertex flux
continuity and interval-integrability, nonnegativity, and continuity of the summed flux. These
are retained verbatim. No large-radius second moment, local absolute continuity, corner
identity, or ODE is inferred.

The four majorant theorems and the final derivative theorem each have axiom reports using only
`propext`, `Classical.choice`, and `Quot.sound`.
