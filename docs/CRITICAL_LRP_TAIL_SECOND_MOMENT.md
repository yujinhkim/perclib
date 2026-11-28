# Tail scales and the second-moment method

`Analysis/SecondMomentCase3/CriticalVolumeTail/SecondMoment/Defs.lean`
describes what the second moment can and cannot prove about the cited critical
tail.

## A sharp per-radius tail bound

`cutLaw_tail_le_secondMoment_div` is the ordinary Markov inequality at the
second moment of the actual cutoff cluster volume. Together with the
probability bound `P ≤ 1`, it gives
`P_{β_c,r}(|K| ≥ n) ≤ (E_{β_c,r}|K|²)^{1/4}/√n`
whenever that second moment is finite.

The crossover lemma `sqrt_mul_min_le_quarterRoot` shows
`√n · min(1,m/n²) ≤ m^{1/4}`. Equality at `m = n²` shows why the exponent
one-quarter is what these two bounds alone give. This does not create a common
constant across radii.

`criticalVolumeTail_of_uniform_secondMoment` then makes the sufficient
condition explicit: a uniform bound `E_{β_c,r}|K|² ≤ K` on all positive radii
gives the uncut critical leaf with constant `K^{1/4}`, and a corresponding
moment gap. Whether that uniform critical second-moment bound can hold is not
established here; it should not be claimed from finiteness at each radius.

## The source consumes a scale-truncated bound

The paper optimizes the first-moment estimate at the scale of the second
moment. `CriticalVolumeTailUpToScale C` demands the tail only at integers at or
below `cutoffScale (cutMoment 2 r).toReal`.

The truncated lemmas reproduce the unchanged head partition, optimization and
explicit `(4C+1)³` constant. `cube_cutMoment_le_of_volumeTailUpToScale` and the
matching `hgm` thus follow without needing the tail beyond the actual truncation
scale. The full cited leaf implies the truncated one. Strictness of that
weakening in a particular model is not asserted, and the truncated leaf itself
is still a hypothesis rather than a proved critical-tail theorem.

## No reverse implication from the moment gap

`exists_momentGap_with_large_tail_envelope` and
`exists_momentGap_not_tailEnvelope` construct an explicit family of finite
three-atom probability distributions. They satisfy `(E X)³ ≤ E X²` while
`√L · P(X ≥ L)` is arbitrarily large. Hence no envelope constant can be inferred
from the moment gap independently.

This is a counterexample to the implication between numerical moment/tail
statements, not a percolation counterexample. It says the cited volume-tail
input is not smuggled into the requested second-moment asymptotic from Jensen
or generic regular variation; its scale-sensitive probabilistic content must
still be formalized.

## Remaining work

The proof of the cited tail bound itself has not been supplied. It needs a
susceptibility/triangle differential inequality and a two-intensity-tail or
cutoff-versus-uncut comparison, not merely this optimization. All 17 binary and
abstract tail-scale exports use standard axioms in the independent rebuild.

## The complementary lower bound

`SecondMoment/Lower` now proves the Paley–Zygmund truncation inequalities in
extended-real arithmetic at both integer and real thresholds. At the model it
bounds the cutoff tail below from finite first and second moments. The
increasing cluster-tail event then transfers these lower bounds to the uncut
critical law, in the correct monotonicity direction.

For first- and second-moment asymptotics, the explicit radius
$r_n=(4n/\kappa)^{1/\alpha}$ yields an eventual $1/(Cn)$ lower bound on
`M.tailProb`, including the frozen `I16rhs` and its extended-real form. The
moment assumptions and positivity of the corresponding constants remain
explicit. This is only an $n^{-1}$ lower result, not the sharper $n^{-1/2}$
asymptotic tail or `CriticalVolumeTail`. The final `twoAtom_sharpness` lemma is
arithmetical, not a full optimality theorem for every probability law, and it
must not be cited as such.
