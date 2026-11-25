# Moments and cutoff derivatives at large radii

`Analysis/Cutoff/OffCorner/LargeRadiusMoments.lean` and
`Analysis/Cutoff/OffCorner/SharpnessThresholdEscape.lean` separate fixed-radius
finiteness from the large-radius asymptotics that the paper actually needs.

## Fixed-radius moment finiteness

For a source model with `β_c > 0`, let

```lean
∀ β < M.betaCrit, (∫⁻ ω, clusterVol ω 0 ∂(M.law β)) ≠ ⊤
```

be the subcritical first-moment hypothesis. Translation invariance of the source
edge probabilities gives the generic fourth-moment tree bound, so the same
hypothesis also supplies a finite fourth moment at every subcritical intensity.
The established reduced-intensity cutoff domination then gives
`M.cutMoment p r ≠ ⊤` for **every positive radius `r` and every `p ≤ 4`**.
There is also an explicit one-reduced-intensity version retaining the finite mean
at that reduced intensity.

For the literal power-law witness, the resulting
`sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_subcritical` gives the
off-corner derivative at **every** positive radius. Its only probabilistic input
is the subcritical first-moment statement above (together with `β_c > 0`); no
finite cutoff moment is assumed at any radius because it is constructed from
`cutMassAt_ne_top_of_subcritical`. The derivative remains off corner and uses
`exclScalar`, not an asymptotic mean-field approximation.

The subcritical first-moment hypothesis is still the formal sharpness input.
Zero percolation probability alone does not imply it in the general product-law
framework, and the available high-temperature interval does not by itself reach
all reduced intensities approaching `β_c`.

## What remains open at large radius

The module proves an explicit pointwise threshold at each subcritical `β`: the
cutoff mean is bounded by `(2α/β) r^α` beyond a radius determined by the finite
uncut mean. This is the immediate consequence of sharpness. It does **not**
produce one threshold uniform in `β` on `[β_c/2, β_c)`. The paper's a priori
bound, bootstrap error estimate, and moment asymptotics therefore remain open.

`SharpnessThresholdEscape.lean` proves that if the subcritical mean diverges as
`β ↑ β_c`, this explicit pointwise threshold is unbounded as a function of `β`.
It is a limitation of the pointwise threshold route alone, not a counterexample
to the paper's uniform bootstrap threshold or asymptotic bound.

Conversely, cutoff moments tend to the uncut critical moment. When that moment
is infinite, there can be no finite bound on the cutoff moments uniform in
radius; if the first critical moment is infinite, every order `p ≥ 1` tends to
`⊤` as `r → ∞`. Finite moments at fixed radius are not sufficient for the
paper's rates.

The stronger `SourceCutoffFourthMoments.lean` additionally states the
unconditional extended-real inequalities `cutMoment 4 r ≤ 15 * cutMoment 1 r ^ 7`
for source norms positively proportional to the lattice sup norm, including the
explicit witness with scale `2`. All new modules passed strict focused checking
with only the standard axioms before integration.
