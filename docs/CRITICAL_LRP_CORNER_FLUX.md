# The direct pivot and summed singleton-flux discontinuity

`Analysis/SecondMomentCase3/RadialRegularity/CornerFlux` proves the
measure-side corner statement at an attained off-diagonal radius, conditional
on strict two-point non-degeneracy.

## Exact direct-edge content

For the direct edge `s(0,y)`, the forced-open connection event is universal.
Its Russo/pivotal mass is therefore `1 - cornerGap`, where `cornerGap` is the
mass of connection after forcing that edge closed. At `r = ‖y‖`, the cutoff
profile gap vanishes, so the edge is almost surely closed and the corner gap is
exactly `τ_{β_c,r}(0,y)`. Hence

```text
directPivot y ‖y‖ = 1 − τ_{β_c,‖y‖}(0,y),
```

and the mass vanishes exactly when the cutoff two-point value is `1`.
Confinement below the attained radius gives a positive direct pivot, and
`τ_{β_c}(0,y) < 1` suffices through cutoff-to-uncut domination. These are
measure-level conditions, not a coefficient positivity trick.

`m8FluxTerm_direct_at_self` computes the derivative-weighted flux at the
attained radius, and `not_continuousAt_m8FluxTerm_direct_of_pos` proves its
jump if that direct pivot and the coefficient are nonzero.

## The jump survives summation

`SumLevel.lean` identifies the left limit of every summand. Shorter edges keep
their value and corner/longer edges vanish from the left. Termwise left limits
are evaluated with existing finite-moment pivotal continuity.

A genuine radius-uniform summable envelope from `RadiusEnvelope`, obtained at
a strictly larger radius with finite first moment and a local derivative bound,
permits Tannery's theorem for the complete singleton flux. The direct corner
term remains in the accounting:

```text
left-limit flux + β_c(-K'(s)) · directPivot y s ≤ firstFlux y s.
```

Thus `not_continuousAt_firstFlux_of_corner` proves a discontinuity of the full
singleton first-moment flux under positivity of the direct pivot. The escape
and strictly-subunit critical two-point variants are included.

## Exact hypothesis boundary

The proof does not provide every input:

* critical intensity and nonzero derivative at the attained radius;
* continuity of `deriv K` there;
* a one-sided derivative bound on `[s/2,s]`;
* a larger radius `ρ > s` with `deriv K ρ < 0` and finite first cutoff moment;
* strict `τ_{β_c}(0,y) < 1`, or a confinement alternative, or positive direct
  pivot itself.

These are explicit retained assumptions. The strict two-point estimate is the
probabilistic residual; a later HD upper bound can provide it at large
displacement. No general existence theorem of such a corner follows merely
from the coefficient jump already proved earlier.

This is a statement about the singleton first-moment flux, not a discontinuity
proof for the entire mass-transport sum and not a jump rate. Summability of all
other edge contributions is necessary to show that the direct mass is not lost
in a countable limit, and it is used rather than glossed over.

All four modules build with strict flags and standard axioms. Write-ups may no
longer claim this package merely identifies a coefficient jump: the summed
singleton discontinuity is conditional on the documented hypotheses only.
