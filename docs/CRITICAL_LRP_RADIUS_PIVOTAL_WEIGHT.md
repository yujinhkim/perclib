# Interval integrability of the total pivotal weight

`Analysis/Cutoff/OffCorner/RadiusPivotalWeight.lean` bounds each summand of the singleton
`sMomentWeight` by the interior-scale envelope of `RadiusEnvelope.lean`:
`weightedTouch_le_env` multiplies the derivative-weight comparison by the monotone touching
probability, and `measurable_weightedTouch` establishes radius measurability without continuity.

`intervalIntegrable_pivotalWeight_of_envelope` proves
`IntervalIntegrable (fun r => sMomentWeight 0 {y} 1 M.cutProb M.cutEdgeDeriv r) volume a' b'`
under `0 < a' ≤ b' ≤ ρ`, a bound `-(deriv M.K r) ≤ C` on `Icc a' b'`, `0 ≤ C`,
`deriv M.K ρ < 0`, `0 < ρ`, and `M.cutMoment 1 ρ ≠ ⊤`. The proof uses `Measurable.tsum`,
summability of the envelope, and `IntegrableOn.of_bound` on the compact window. It estimates the
actual total pivotal weight, not just the singleton flux.

`hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope` supplies this `hboundint` on all
subintervals of `Ioo α β`, in either endpoint order, using comparison radius `β`, a finite second
cutoff moment at `β`, a bound on `-deriv M.K` throughout `Ioo α β`, and `deriv M.K β < 0`. Its
remaining regularity inputs are exactly the per-vertex flux continuity `hcontinf` and summed-flux
continuity `hGcont` of the endpoint theorem, alongside these explicitly retained envelope data.

This is a conditional regularity input for the off-corner endpoint derivative. It does not
supply a comparison radius or its derivative sign, prove a finite large-radius first moment,
remove `hcontinf` or `hGcont`, establish complete Russo differentiation or an ODE, or settle
corner behavior. In particular, endpoint second-moment finiteness does not itself supply the
negative derivative sign required by the envelope.

For windows past the source tail threshold, `OffCorner/RadiusTailDeriv` derives the local slope
bound and comparison sign from `exists_deriv_bounds`; see
`docs/CRITICAL_LRP_RADIUS_TAIL_DERIV.md`. That specialization still requires its endpoint moment
and both flux-continuity premises.

The new declarations compile with the strict project flags and depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
