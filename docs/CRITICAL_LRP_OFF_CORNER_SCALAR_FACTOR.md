# Off-corner scalar factor and endpoint inputs

Integrated from the accepted `smwuges40/m8` packet in
`Analysis/Cutoff/OffCorner/ScalarFactor/{Defs,Main}.lean`.

`exclScalar r` is `(exclMass r).toReal`, `coeffRHS r` is `β_c (-K'(r))`, and
`rhsScalar r` is their product. `exclMass_le_ball_mul_cutMoment_two` gives, for every `r ≤ b`
with `cutMoment 2 b ≠ ⊤`,

`exclMass r ≤ #(ball b) * (cutMoment 2 b)^2`.

This uses the actual moment bound inside `E1Sign.exclMass_le`, not a fixed upper moment across
radii. Real-valued conversion is guarded by finiteness at the endpoint, and `exclMass_ne_top_of_le`
gives the whole-window finiteness statement. `connMass_le_window` also records the unconditional
extended-nonnegative connected-mass bound.

`abs_rhsScalar_le_of_window` combines this with an explicit bound on `|deriv K|` on a compact
window to dominate the scalar factor by the endpoint data. It is a bound on the derivative value,
not on any uniform incident degree.
`continuousAt_rhsScalar_iff` further isolates the scalar continuity requirement: with positive
`β_c`, continuous nonzero `deriv K`, continuity of the scalar factor is equivalent to continuity
of the excluded mass. No such continuity is supplied. In particular `K_diff` alone is not
continuity of the derivative, and `ConnMassRegularity` does not prove this excluded complementary
mass is continuous, especially at sphere radii.

The endpoint derivative wrapper
`hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_endpoint` needs the second moment **only at the
upper endpoint** rather than at each interior radius; monotonicity supplies it at interior points.
It deletes `hfluxnn`, proves `hmeasinf` and `hfluxintW` from per-vertex flux continuity, and retains
`hboundint`, `hmeasK`, `hcontinf`, and `hGcont`. The off-corner and differentiability hypotheses
remain. A scalar-named version uses `rhsScalar`.

This is still a conditional off-corner Russo derivative, not a complete ODE, a proof of remaining
continuity/measurability inputs, or a large-radius moment-existence theorem.

All 16 axiom reports across `Defs` and `Main` use only
`propext`, `Classical.choice`, and `Quot.sound`.
