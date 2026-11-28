# Displacement and gyration moments: exact identities and uniform bounds

`Analysis/GyrationMoments/Defs.lean` starts the §I.5 spatial-moment analysis
with input the paper actually uses: the infinite-volume spatial moment and the
two-point function of the normalized cutoff law.

## Exact identities

For any countable vertex set, any Bernoulli edge profile and any nonnegative
(extended-real) weight, `lintegral_tsum_indicator_cluster` proves by Tonelli's
theorem that
`∫ Σ_{y∈K_o} w(y) = Σ_y w(y) τ(o,y)`.

`displacementMoment_eq_tsum` evaluates the even spatial power
`Σ_{x∈K_0} ‹x,u›^(2p)` as the two-point sum with that weight. There is also a
real-valued form, a definitional identification with production's
`spatialMomentENN`, a first-moment consistency check at `p = 0`, and the exact
gyration numerator and ratio formulas. `xi2sq_eq_tsum_ratio` expresses the
radius of gyration as the weighted two-point sum divided by the cutoff
susceptibility.

`ofReal_pow_mul_tsum_indicator_le_displacementMoment` controls the far part of
the two-point mass by the displacement moment and needs no summability of that
far part.

## Uniform radius bounds and convergent spatial moments

`Analysis/GyrationMoments/Limit.lean`, accepted after independent review from
`smwzt36y2/m4`, adds the missing converse to the one-sided cutoff comparison.
For monotone extended-nonnegative weights it proves the exact sup/`tsum`
interchange without integrability assumptions, using directed suprema and the
finite-cluster exhaustion. In particular `uncutTwoPointE M y = ⨆_r cutTwoPointE M r y`,
and

```text
gyrationMomentUncut M = ⨆_r gyrationMoment M r
```

for every model, with `Tendsto (gyrationMoment M) atTop (𝓝 gyrationMomentUncut M)`.
The new `displacementMomentUncut M p u` has the same supremum and limit statements
for every even displacement moment. The real-valued limits additionally require
finiteness of the uncut numerator. Consequently a radius-uniform finite cutoff
bound on either numerator exists exactly when its uncut numerator is finite;
this does not establish that finiteness for a canonical lattice.


`cutTwoPointE_mono` and `gyrationMoment_mono` record monotonicity in the cutoff
radius. `cutTwoPointE_le_uncut` and `gyrationMoment_le_uncut` bound every cutoff
numerator by the uncut critical one. Even the radius-supremum is controlled by
that uncut moment. Thus *if* the uncut gyration numerator is finite, every
cutoff numerator has one radius-independent bound.

The one-sided bounds alone did not imply convergence or uncut finiteness. The
new exact supremum identity supplies the converse route; it still does not
supply finiteness of the uncut spatial moment for the canonical lattice.

## A useful obstruction

The profile arising from the uncut power law on a unit-volume ball produces a
coefficient different from Proposition I.5.2's `α/(2−α)` unless
`α(d+1) = 2`. The kernel-checked algebra is an obstruction to substituting that
profile into the proof, not a counterexample to the proposition. The cutoff
spatial two-point function or its ODE is what must be estimated.

## What remains open

This package does not prove Lemma I.5.7 (the gyration ODE), its required signed
cancellation, two-point asymptotics, Proposition I.5.2, or any superprocess
limit. All 23 audited exports use the standard three Lean axioms. The integrated
module builds with `--wfail` under its production import.
