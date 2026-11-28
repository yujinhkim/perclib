# Cutoff-flux corners and conditional continuity

`Analysis/SecondMomentCase3/RadialRegularity/CornerContinuity` audits the
literal radial-continuity interface at attained radii. It was rebuilt at
`bd25afb1130f7fe93446b447f9a68a4d3aba08cc`.

## Coefficient versus full sum

For an off-diagonal edge, `cutEdgeDeriv` vanishes strictly below the edge's
attained radius and equals `β_c(-K'(r))` at that radius. Its left limit is thus
`0`; the right-hand formula gives the nonzero derivative value. Consequently
`m8_not_continuousAt_cutEdgeDeriv_at_dist` proves discontinuity whenever the
critical intensity and derivative are nonzero. The model's error
representation makes the derivative nonzero eventually, while attained radii
are unbounded and countable. Away from the corner set, coefficient continuity
follows from continuity of `deriv K`.

This proves a **summand** discontinuity, not that the summed flux must be
discontinuous. The report's discussion of a nonzero corner sum is included as
an observation, not as an established non-vanishing theorem about the whole
flux. No claim is made that every existing `hcontinf` premise is logically
false.

## Corrected conditional interface

`m8_continuousAt_tsum_of_locally_dominated` gives continuity from termwise
continuity and a single summable dominator valid on a neighbourhood, rather
than assuming a global bound. `m8_hcontinf_corrected` and its almost-everywhere
counterpart apply this to the actual flux at radii outside the attained set,
with `hK`, pivotal-flux continuity, and local domination still explicit.
These are genuine residuals; no finite-range blanket assumption or pointwise
window limit is converted into uniform convergence.

`m8_hcontinf_iff_uniform_windowTail` isolates the missing quantitative input:
under monotone window approximations with pointwise convergence and radius
continuity, continuity of the limiting flux is equivalent to a local,
radius-uniform window-tail estimate. This is why pointwise convergence alone
cannot discharge the radial-continuity premise.

The package does not prove pivotal-flux continuity, the local dominator, the
derivative's continuity from the paper's merely measurable error function, or
any full summed-flux discontinuity. All its conditional continuity exports and
discontinuity proofs use only `propext`, `Classical.choice` and `Quot.sound`.
