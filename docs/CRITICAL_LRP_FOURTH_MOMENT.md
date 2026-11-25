# The ordinary fourth-moment tree-graph inequality

`Correlation/FourthMoment/` proves the `p = 4`, `k = 0` instance of the
tree-graph moment bound used in Lemma I.4.16. It was completed by Ultramath
`smwpj8umm` members m1 and m2, with the diagram/moment assembly checked during
integration.

Let `V` be a countable abelian group and let `π : Sym2 V → unitInterval` specify
an arbitrary independent Bernoulli bond law. Assume its two-point function is
translation invariant:

```text
tau π a b = tau π 0 (b - a).
```

The exported theorem `FivePoint.fourth_moment_le` proves

```text
∫⁻ ω, cardFun(cluster ω 0)^4 ∂law π
  ≤ 15 * (∫⁻ ω, cardFun(cluster ω 0) ∂law π)^7.
```

All quantities are in `ℝ≥0∞`; no moment-finiteness or local-finiteness
hypothesis is needed. The parameter `β` and weights of the application are
encapsulated in `π`. The source package remains a partial formalization: this
is one order and one mixture class, not all of Lemma I.4.16.

## Deterministic five-point realization

`Arms.lean` and `Attach.lean`, supplied by m1, prove:

```text
exists_combShape :
  ∀ T : Fin 5 → V,
    (∀ i, G.Reachable (T 0) (T i)) →
    ∃ k : Fin 15, ∃ u v w, CombShape G k u v w T.
```

The argument uses a four-terminal H-shaped arm decomposition, join-reduced
first-hit attachment of the fifth terminal, and a case analysis over the four
arms and their spine. `attachAny` splits the hit arm and preserves its edge
`Nodup` invariant. `combSlots_swap01`, `combSlots_swap34`, and
`combSlots_reverse` normalize the resulting five trees to the fifteen literal
slot patterns, allowing coincident vertices and empty spines.

`Bridge.lean` turns the first slot into `CombWitness` and the middle slot into
`BalWitness`, preserving pairwise edge-disjointness. Hence
`harm5_of_combShape` discharges the complete fifteen-shape deterministic input
rather than merely stating it. The native connected-cluster form is
`exists_combShape_connects`.

## Probability and moment assembly

* `prodBernoulli_seven_wit_le` applies countable-product BK to seven increasing
  events with seven pairwise-disjoint finite open certificates. m2 supplied
  this companion to the existing five-fold statement.
* `CombEvent` and `BalEvent` represent the twelve comb and three balanced
  labelled trees. `combEvent_le` and `balEvent_le` bound each by its
  seven-factor tree sum, with no finiteness or homogeneity assumption.
* `five_point_le_of_harm` assembles all fifteen shape probabilities. A fixed-pair
  corollary `five_point_le_of_pair` is retained as a separate conditional helper.
* Translation-invariant row and column sums evaluate each leaf-summed tree
  diagram to exactly `X^7`, where `X = ∑' x, tau π 0 x`.
  `tsum_fivePointDiagram` therefore evaluates the collective diagram to
  `15 * X^7`.
* `lintegral_cardFun_four_eq` expands the fourth cluster power as the fourfold
  sum of joint connection probabilities. The remaining step is the comparison
  of mean-cluster transportation notation with `X`; there is no truncation to
  finite configurations and no hidden almost-sure-finiteness premise.

Compiled `PUnit` examples witness `CombWitness`, `BalWitness`, and `Harm5`, so
these new definitions are non-vacuous. The actual arbitrary-simple-graph
realization is proved separately by `exists_combShape`.

## What remains open

This does **not** prove the mixed-moment instances `k = 1` or `k = 2`, which
require the distinguished-internal-vertex/three-star regrouping of Lemma
I.4.16. In particular, the present result is weaker than

```text
E|K|⁴ ≤ 15 E|K|² (E|K|)^4
```

and it proves no all-order statement. It also does not supply a uniform
subcritical first-moment bound, sharpness at the critical threshold, or either
of the paper's two principal moment roots.
