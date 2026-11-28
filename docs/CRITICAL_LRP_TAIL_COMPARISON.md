# The critical tail from two explicit probabilistic inputs

`Analysis/SecondMomentCase3/CriticalVolumeTail/TwoIntensityComparison` proves the
uncut critical-tail envelope and its Case-3 moment-gap consumer from two named
inputs. Both remain hypotheses; neither is instantiated for the canonical model.

## The actual source comparison

The underlying source is T. Hutchcroft,
[*On the derivation of mean-field percolation critical exponents from the
triangle condition*](https://arxiv.org/abs/2106.06400), J. Stat. Phys. 189 (2022) 6.
For normalized one-arm weights its displayed comparison is

```text
P_{β₂}(|K| ≥ n) ≤ (2/n + 4/β₁ · |β₂ − β₁|²) χ_{β₁},   β₂ ≥ β₁ > 0.
```

The model-level `TwoIntensityTailComparison A` states this with the coefficient
scaled by the nonnegative one-arm sum `A`. This matches the source's rescaling
of the edge weights. `SusceptibilityBound K` is the separate mean-field bound
`χ_β ≤ K/(β_c − β)` for `β < β_c`.

The relative-entropy and decision-tree proof of these inequalities is not
formalized here. In particular, this module does not prove the triangle
condition, generalized susceptibility upper bound, or a source graph instance
satisfying the two premises simultaneously.

## What the Lean proof establishes

For `β_c > 0`, `A ≥ 0` and `K ≥ 0`, choose `β₁ = β_c − n^{-1/2}` for sufficiently
large $n$. Then $\beta_1 \ge \beta_c/2$ and $\beta_1 < \beta_c$. The comparison
and the susceptibility bound give a finite universal envelope. For small $n$,
use $\mathbb P \le 1$ and a constant large enough to dominate it. The outcome is
literally `CriticalVolumeTail C` with

```text
C = max 1 (max (2/β_c) (2K + 8 A K / β_c)).
```

The explicit arithmetic is
$$P_{\beta_c}(|K_0| \ge n) \le C n^{-1/2},$$
but this is a proved deduction from the named inputs, not a proof of those
inputs. The source normalization is carefully handled: there is no cutoff law,
no backward cutoff-to-uncut monotonicity, and no inference from a radius-bound,
from finite critical mean, or from zero percolation probability.

The additional `exists_case3_hgm_of_twoIntensityComparison` invokes the already
proved consumer with the same finite-critical-tail input removed. It retains
`h2 : ∀ r ≥ 1, M.cutMoment 2 r ≠ ⊤`, and it does not extend this finiteness to all
nonnegative radii or derive asymptotics. Thus Case 3 remains PARTIAL rather than
being declared complete from a named citation.

## Seven-terminal realization and the I.4.16 residual

`Correlation/SixPoint/SevenPoint` supplies an unconditional graph-theoretic
ingredient: a joint connection of seven terminals realises one of 840 arm
systems, made of nine edge-disjoint walks. Arbitrary collapsed tuples are
allowed, so the construction directly avoids the refuted hub-collapse mechanism
without changing the intended graph.

Its event-probability union bound is proved. The coefficient comparison
$15\cdot7\cdot8=840 \le 945$ is explicit, but no moment exponent follows yet.
The missing bipartite-class/star regrouping and the exact BK evaluation to
$(E|K|^2)^2(E|K|)^5$ remain. A naive joint/single-factor grouping would give the
weaker $\chi^6$ factor. The actual mixed sixth moment thus remains unproved.

# The summation step of Lemma I.4.11

`Correlation/I411/RowSumCore` and `Correlation/I411/RowSum` formalize the
summation/factorisation stage of Lemma I.4.11 in the project namespace
`PercLib.CriticalLRP.I411`. They do **not** identify the original cluster
numerator with the five-factor gap diagram and therefore do not prove the
whole lemma.

## Finite real-valued vertices

`gapLeaf τ o x y z` is the five-factor tree diagram
$$τ_{oa} τ_{ax} τ_{ab} τ_{by} τ_{bz},$$
summed over $a,b$, and `gapMass τ o B` sums it over $y\in B$ and all $x,z$.
The module proves that exchanging summations and factoring the separated
variations gives
$$\sum_{x,z}\mathrm{gapLeaf}(x,y,z)
 = \sum_{a,b} τ_{oa}τ_{ab}τ_{by}\,(\sum_xτ_{ax})(\sum_zτ_{bz}).$$
Two row bounds $\sum_{\bullet}τ_{a\bullet}\le χ$ therefore give
$$\mathrm{gapMass}\le χ^2\sum_{y\in B}∇(0,y).$$
`lemma_I_4_11_step` also carries out the division by $|B|χ^2$, correctly
assuming a nonempty window and positive susceptibility.

With row sums equal to χ the factorisation is equality. The Unit example uses
`τ = 1`, `B = {()}` and `χ = 1`, and attains the bound, so the summation API has
a genuinely inhabited instance rather than a degenerate inference.

## Countable extended-real vertices

The companion extended-nonnegative version needs no finiteness assumption:
Tonelli identities and the row bound in `ℝ≥0∞` give the same bound over an
arbitrary finite window and all $x,z$. This is not a claim that it converts
extended moments into finite real moments.

The remaining model-specific work is the two-copy rewriting of the numerator of
the excluded mass, plus the pointwise gap inequality (I.4.12). Both are kept
outside this summation result; neither is silently discharged by the χ²
factorization. The source lemma consequently remains PARTIAL.

## Subsequent per-edge proof

`Entropy/PerEdgeKL` now proves the exact exponential-parameter KL bound of source
Lemma 3.3/(3.4), with denominator $2\min\{a,b\}$ and the appropriate one-edge
model instantiation. `Entropy/Pinsker` and this per-edge result discharge the
analytic comparison and upper per-edge ingredients respectively. They do not
provide the transcript revealment estimate or the external susceptibility bound.

## Finite transcript entropy and assembly (subsequent results)

`Entropy/TranscriptKL` proves fixed-depth fresh-query fibre identities and the
corresponding entropy chain rule, with the revealment probability weighted at
the lower intensity as in the source. `Entropy/TranscriptEntropy` discharges its
per-edge input using `PerEdgeKL`. `Entropy/TailAssembly` then proves the finite
and countable assembly, including degenerate event masses, exact finite tail
sums, and the finite weighted-Bernoulli instantiation. The conditional inputs
to that assembly are named `hKL` and `hRev`; cluster-event construction,
revealment and infinite-volume convergence remain outside the completed step.

## Finite log-sum and Pinsker ingredients

See [the entropy note](CRITICAL_LRP_ENTROPY_CORE.md). The package proves the
finite product-model normalisation, exact cylinder mass, log-sum, and sharpened
binary/generalised Pinsker inequalities. These are finite analytic ingredients
for the relative-entropy proof, not a completed decision-tree revealment
argument or the two-intensity comparison itself.
