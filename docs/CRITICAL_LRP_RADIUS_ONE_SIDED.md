# One-sided bounds for the infinite singleton flux

Accepted from Ultramath `smwuinbxz`, member `m2`. Module:
`Analysis/Cutoff/OffCorner/RadiusOneSided.lean`.

Touching-event probabilities are monotone in the cutoff radius, with explicit one-sided
inequalities. `cutEdgeDerivLeft_nonneg` and `abs_cutEdgeDerivLeft_le_cutEdgeDeriv` compare the
strict left edge weight with its closed counterpart. The strict weight omits exactly the shell at
the attained endpoint.

`abs_sMomentInfFlux_le_strictWeight_at_endpoint` bounds infinite-volume absolute singleton flux
at `r ∈ [a', r0)` by a scaled sum at `r0` using the strict weight. Its proof uses the existing
pivotal-flux majorant, monotonicity of touching probabilities, and a finite first cutoff moment
at `r0`; it does not require finite-window continuity. With continuity of `deriv M.K` explicitly
assumed, an epsilon-collapse version gives a `(1 + ε)` factor of the same strict total. Another
comparison bounds the strict total by the closed total.

These are **left-sided upper bounds**, not proofs of `hcontinf`, `hGcont`, ordinary continuity,
a lower oscillation bound, or a matching right-sided result. Monotone law domination controls
touching probabilities, but not the difference-of-increasing-events appearing in pivotal flux.
The explicit remaining analytic input is one-sided continuity of normalized pivotal edge terms;
it is not supplied here.

The 546-line proof module was independently rebuilt with the strict project flags. All ten
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
