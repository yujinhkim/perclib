# Mixed tree-moment bounds

`Correlation/CubicMixed` proves the `p = 3`, `k = 1` instance of the
regrouped tree-graph inequality associated with Lemma I.4.16, and
`Correlation/FourthMoment/Mixed` proves the `p = 4`, `k = 1` instance,
and `Correlation/FourthMoment/MixedK2` proves the `p = 4`, `k = 2` instance.
`Correlation/FourthMoment/Bridge` separately proves the ordinary `p = 4`,
`k = 0` bound, and `Correlation/SixPoint/Attachment` proves the `p = 5`,
`k = 1` bound.

## What is proved

Let `V` be a countable abelian group with independent bond law `law π` and
translation-invariant two-point function `tau π a b = tau π 0 (b - a)`.
`TreeExpansion.third_moment_mixed_le` proves, in `ℝ≥0∞` and with no
moment-finiteness premise,

```text
∫⁻ ω, cardFun(cluster ω 0)^3 ∂law π
  ≤ 3 * (∫⁻ ω, cardFun(cluster ω 0) ∂law π)^2 *
      ∫⁻ ω, (cardFun(cluster ω 0))^2 ∂law π.
```

This uses the same native configuration and cardinality conventions as the
ordinary third-moment theorem. The right-hand product is
$3(\mathbb E|K_0|)^2 \mathbb E|K_0|^2$ exactly, without quotienting by some
third moment and without replacing the native second moment by a BK product.

## Proof structure

* `shapeWitness_starPair` combines the two root-facing walks through the first
  branch vertex with their spine. The resulting joint certificate is disjoint
  from the untouched two remaining arms. This is the deterministic star-pair
  regrouping, not an independence assertion.
* `starPairEvent_le` bounds it by the joint probability of the two root-facing
  arms and the two remaining two-point functions. Threefold BK handles the three
  disjoint certificate groups.
* `triple_le_starSum` covers all three labellings of the four-leaf binary tree,
  using the proved native arm decomposition.
* `lintegral_cardFun_sq_eq` is the exact Tonelli expansion of the native second
  cluster moment into a double sum of connection events.
* `joinSum_eq_cardFun_sq` proves that the star-pair function
  `∑' x, ∑' w, law π (conn 0 w ∩ conn x w)` is **exactly** this native second
  moment. Both events say that `x` and `w` lie in `0`'s cluster, hence are
  connected to `0`; one implication follows by transitivity and the other needs
  symmetry as well. No nonstandard graph argument is needed for the equality.
* `tsum_starTerm_factor` evaluates the remaining two free arms to $\chi^2$,
  where $\chi = \sum_x tau(0,x)$, without assuming finiteness. Summing all three
  labellings then produces the factor $3\chi^2$ multiplied by the native second
  moment.

The initial worker report left an obstruction after keeping the star function as
an unnamed quantity. The later integrator proof checked the exact equality above
and completed the target. That earlier absence of a bridge is not treated as a
reason to reinterpret the paper or to replace its printed inequality by a weaker
one.

## The fourth-moment mixed case

Under the same native hypotheses,
`FivePoint.fourth_moment_mixed_le` proves

```text
∫⁻ ω, cardFun(cluster ω 0)^4 ∂law π
  ≤ 15 * (∫⁻ ω, cardFun(cluster ω 0)^2 ∂law π) *
      (∫⁻ ω, cardFun(cluster ω 0) ∂law π)^4.
```

Thus the coefficient is $5!!=15$ and the two exponents are $k=1$ and
$2p-1-3k=4$, exactly as in Lemma I.4.16. There is no second-moment
translation-invariance or moment-finiteness premise.

The proof uses two fivefold BK regroupings of the seven-edge `CombSlots`
realizations. When the root occupies the shallow slot, the joint pair is
certified through the shared first spine. When it occupies the middle slot,
the joint event is `conn root w ∩ conn u w`, certified by the root-to-`w`
and `u`-to-`w` walks through the shared second spine. In either case the
unused branch vertex disappears inside the joint certificate and is handled
by a union bound, not dropped with an unconstrained sum. Four remaining
single arms then supply exactly $\chi^4$.

`tsum_slotDiagram` evaluates all fifteen leaf-labelled patterns to the same
product. `joinSum_eq_cardFun_sq` converts the retained joint sum to the native
second moment, while `tsum_fin_four_swap`, Tonelli and `chi_eq_tsum_tau`
assemble the native fourth moment. `Mixed/Defs.lean` contains the diagram
and certificate definitions; the proof-only `Mixed.lean` contains the
inequalities and summation arguments.

## The `p = 4`, `k = 2` case

`FivePoint.fourth_moment_mixed_k2_le` proves

```text
∫⁻ ω, cardFun(cluster ω 0)^4 ∂law π
  ≤ 15 * (∫⁻ ω, cardFun(cluster ω 0)^2 ∂law π)^2 *
      ∫⁻ ω, cardFun(cluster ω 0) ∂law π.
```

The hypothesis is now genuinely stronger than translation invariance entirely at
the level of `tau`: it is full simultaneous translation invariance of the opening
profile,
`hq : ∀ x y g, π s(x+g,y+g) = π s(x,y)`. The two common-centre second-moment
factors require this full law invariance, but there is no separate `h2`, moment
finiteness, fixed-centre, or shape hypothesis.

Each normalized `CombSlots` realization splits into three groups. One group
certifies the shallow joint pair through their shared first spine, one is the
middle singleton arm, and one certifies the deep joint pair through the reversed
second spine. All three groups share the middle centre. Threefold BK consumes
seven original walks as `3 + 1 + 3`, and the other two branch vertices disappear
inside the groups and are removed by union bounds rather than summed.

`secondMoment_root_independent` derives root independence of the second moment
from `hq`. `slotDiagramK2` and `tsum_slotDiagramK2` then evaluate all fifteen
leaf-labelled patterns to `secondMoment π 0 * ((∑' x, tau π 0 x) * secondMoment π 0)`.
Finally `fourPoint_le_slotSumK2`, `lintegral_cardFun_four_eq`, and the finite
`Fin 15` sum give the exact coefficient and exponents
$5!!=15$, $k=2$, and $2p-1-3k=1$. The six modules under
`Correlation/FourthMoment/MixedK2/` separate definitions, transport, sums, leaf
patterns, certificates, and final assembly. Two independently rebuilt complete
proofs established this case, so the admissible `p = 4` range `k = 0,1,2` is now
complete in the model classes stated above.

## The `p = 5`, `k = 1` case

`SixPoint.fifth_moment_le`, in
`Correlation/SixPoint/Attachment/Assembly.lean`, now proves

```text
∫⁻ ω, cardFun(cluster ω 0)^5 ∂law π
  ≤ 105 * (∫⁻ ω, cardFun(cluster ω 0)^2 ∂law π) *
      (∫⁻ ω, cardFun(cluster ω 0) ∂law π)^6.
```

Under full profile invariance `hq` on a countable abelian group, the coefficient
is $7!!=105$ and the first-moment exponent is $2p-1-3k=6$. No moment-finiteness,
missing-cover, or extra second-moment-invariance premise occurs.

`Attachment/Cover.lean` constructs a deterministic six-terminal cover by attaching
a sixth terminal to one of seven arms of each of the fifteen five-terminal
patterns, giving `Fin 15 × Fin 7`. `Attachment/Main.lean` keeps the joint pair as
one BK group and bounds the other six two-point events. Each slot evaluates to
`secondMoment π 0 * (∑' x, tau π 0 x)^6`. `Attachment/Final.lean` performs the
repeated finite-index permutations by explicit adjacent extended-sum exchanges;
the assembly uses `tsum_fin15_fin7_const` for the exact `105` count. The fork-shape
proof is not used as the complete cover.

## The ordinary `p = 5`, `k = 0` case

`SixPoint.fifth_moment_ordinary_le`, in
`Correlation/SixPoint/Ordinary/Assembly.lean`, proves the ordinary bound

```text
∫⁻ ω, cardFun(cluster ω 0)^5 ∂law π
  ≤ 105 * (∫⁻ ω, cardFun(cluster ω 0) ∂law π)^9.
```

This is independent of the mixed bound. `Ordinary/NineFold.lean` proves the
finite-family BK interface, and `NineShape.lean` applies it to the nine disjoint
walks of the existing attachment cover. Every diagram has nine `tau` factors,
with no joint pair or second-moment term. `Ordinary/Eval.lean` and `Main.lean`
sum the five free leaves and four internal vertices to exactly `χ^9`, while
`Ordinary/Consumer.lean` carries out the native fivefold Tonelli and `Fin 15 × Fin 7`
accounting. The canonical specialization is
`latticeLongRange_fifth_moment_ordinary_le_uncond`. Thus, in the stated model
classes, the complete `p = 5` range `k = 0,1` is now proved; no finite-moment
premise or full-paper/general-`p` completion is claimed.

## Moment invariance and complete `k` ranges

`MixedK2/RootIndependence.lean` also proves the general covariance statement
`lintegral_cardFun_pow_root_indep`: a measure-preserving relabelling with
cluster covariance fixes every power of cluster cardinality, not just the
second moment. `secondMoment_root_independent_of_hq` gives another derivation
of the two-power form used above, and `tau_eq_root_sub` derives the two-point
translation formula from full profile invariance.
`Correlation/SecondMomentPermutation.lean` generalizes the covariance from
translations to any profile-preserving vertex permutation.
`lintegral_cardFun_pow_permConfig` proves invariance of every cluster moment
power, and `secondMoment_torus_root_independent` instantiates it on a finite
transitive torus without a lattice structure or finiteness premise.

`Correlation/FourthMoment/Cases.lean` packages the complete admissible ranges
explicitly. `third_moment_all_k_le` states, for every natural `k ≤ 1`,
`E|K|^3 ≤ 3 (E|K|^2)^k (E|K|)^(5-3k)` under two-point translation invariance.
`fourth_moment_all_k_le` states, for every natural `k ≤ 2`,
`E|K|^4 ≤ 15 (E|K|^2)^k (E|K|)^(7-3k)` under full profile invariance. These are
finite instantiations of Lemma I.4.16 at `p = 3,4`, not the general-p theorem.
The attachment package separately proves the `p = 5, k = 1` inequality; it does
not assert the other admissible `k` at `p = 5` or any general-`p` statement.

## Canonical power-law instantiation

`CriticalLRP/PowerLawTreeMoments.lean` specializes these statements to the paper's
canonical law on `ℤ^d`. For every `d`, `α` and `β : ℝ≥0`,
`lrKernel_tau_eq_zero_sub` supplies the required two-point translation formula,
and `latticeLongRange_third_moment_le`,
`latticeLongRange_third_moment_mixed_le`,
`latticeLongRange_fourth_moment_le`,
`latticeLongRange_fourth_moment_mixed_le`, and
`latticeLongRange_fourth_moment_mixed_k2_le`, and
`latticeLongRange_fifth_moment_mixed_le` provide the corresponding first six
bounds. `Ordinary/Assembly.lean` additionally provides
`latticeLongRange_fifth_moment_ordinary_le_uncond`, and `SixPoint/Cases.lean`
packages all admissible cases at `p = 5` as `latticeLongRange_fifth_moment_all_k_le`.
Thus the full admissible ranges at `p = 3,4,5` are available at the canonical law. The ordinary third bound is the `p=3,k=0` case, and the mixed third
bound is the `p=3,k=1` case; since $\lceil(3-1)/2\rceil=1$, this covers the
entire admissible $k$-range at $p=3$ in the canonical model. The three fourth
bounds also cover the complete `p=4` range `k=0,1,2` in this model.
`latticeLongRange_third_moment_all_k_le` gives the quantified formula for every
natural `k ≤ 1`, and `latticeLongRange_fourth_moment_all_k_le` gives it for every
natural `k ≤ 2`, with exponents `5-3k` and `7-3k` respectively.

With an explicitly supplied finite-first-moment premise, the same module also
proves `latticeLongRange_third_moment_ne_top_of_firstMoment`,
`latticeLongRange_fourth_moment_ne_top_of_firstMoment`, and
`latticeLongRange_fourth_moment_mixed_ne_top_of_firstMoment`. These are
conditional finiteness corollaries, not a proof of sharpness throughout
$\beta<\beta_c$.

`lrKernel_unitInterval_translation_of_pair` also proves the stronger
simultaneous-translation identity of opening probabilities used by the
second-moment invariance argument for the $k=2$ case. These are actual canonical
model instantiations, not merely generic hypotheses left uninstantiated.

## What remains open

The general-$p$ and full-$k$-range statement, full sharpness on
$\beta<\beta_c$, and the paper's two main moment asymptotics remain open. The
completed third- and fourth-moment instances, and the two completed $p=5$ cases,
are not substituted for the general lemma nor for these missing probabilistic inputs.
