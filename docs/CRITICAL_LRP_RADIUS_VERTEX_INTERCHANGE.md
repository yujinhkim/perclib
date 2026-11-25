# Radius/vertex integral exchange for the cut mass

Production: `Analysis/Cutoff/OffCorner/RadiusVertexInterchange.lean`.

The target is not the already available derivative formula: it is the real integral of
the outer vertex sum of singleton pivotal fluxes under transient cutoff variation.
For a monotone vertex exhaustion `T` and edge exhaustion `S`, on an off-corner window
`Ioo α β` with `0 < α` and `[a,b] ⊂ Ioo α β`,
`intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_cutMoment_two` proves, from a finite
second cutoff moment at `β`,

```lean
∫ r in a..b, (∑' y, sMomentInfFlux 0 {y} 1 M.cutProb M.cutEdgeDeriv r)
  = M.cutMassReal b - M.cutMassReal a
```

The explicit witness theorem
`sourceModelWitness_intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_firstMoment` gives the
same identity with the sole moment input `cutMoment 1 b₀ ≠ ⊤`; the native cutoff-moment
bound supplies the necessary second moment internally.

## Exchange hypotheses eliminated

- **Nonnegativity:** realized by `sMomentInfFlux_eq_toReal_tsum`, using a finite first
  moment and the nonnegative singleton moment functional.
- **Interval integrability:** follows from per-vertex continuity on the closed compact
  interval, not from `hboundint` or from a separate edge interchange.
- **Pointwise vertex summability:** follows from `summable_sMomentInfFlux_of_cutMoment_two`
  at off-corner radii, using the mixed/second-moment domination.
- `hboundint` remains an independently supplied input to the finite-observation exchange.
  It is not mistaken for the radius/vertex interchange.

The resolution uses the already landed monotonicity and `IntegralFluxInterchange`
interfaces, not an invented zero tsum or a finite-volume replacement of the
infinite-volume cutoff.

## Actual flux versus weighted touching bounds

When nonzero, the unit-weight singleton `sMomentWeight` is a nonzero constant family in
`y`, so it is not summable on the infinite lattice. The actual per-vertex fluxes can be
summable under finite second moment. This shows why the weighted touching bound alone
cannot justify the vertex ordering, while it does not contradict interchange through
actual fluxes. The distinction is recorded by
`not_summable_sMomentWeight_singleton_of_pos` and
`summable_sMomentInfFlux_and_not_summable_weight`.

Nothing here proves an attained-radius derivative, creates subcritical sharpness, or
proves large-radius asymptotics. Strict focused checking has no nonstandard axioms.
