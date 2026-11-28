# Case-1 tail: partial analytic scale calculation

`Analysis/SecondMomentCase1/TailScale` supplies two scale estimates and their
Stirling/logarithm prerequisites for the single-cluster tail calculation. It
does **not** prove `CaseOne.SingleClusterTail` or instantiate it at the cutoff
law.

With $m=E|K|$, $u=n/m^2$, and $D(q)=(2q-3)!!$, the tree-moment/Markov bound has
the scale form $D(q)m^{2q-1}n^{-q}=D(q)u^{-q}/m$. The target prefactor is
$\sqrt{2/(um)}\exp(-u/4)$. The needed local comparisons include an extra $m$
on the right, correct when $m\ge1$.

The proved ingredients are:

* `oddDFact_le_two_pow_mul_factorial`: the finite-product coefficient satisfies
  $D(q)\le 2^{q-1}q!$, with `oddDFact` explicitly defined by that product.
* `factorial_le_exp_mul_sqrt_mul`: for $q\ge1$,
  $q!\le e\sqrt q\,(q/e)^q$, from the Stirling sequence's antitonicity.
* `log_six_ge` and `log_105_le`: the numerical logarithm bounds used below.
* `scale_two`: $1\le u^2\sqrt{2/u}e^{-u/4}$ for $1\le u\le6$.
* `scale_five`: $105\le u^5\sqrt{2/u}e^{-u/4}$ for $6\le u\le16$.

The submitted note claimed more API than it contained. In particular, the
present file defines the finite-product `oddDFact` but does not prove its
identity with `Nat.doubleFactorial`, does not carry a theorem named
`oddDFact_three`, and does not contain the final Markov assembly. Reviewer-added
axiom checks for the declarations actually present all show only `propext`,
`Classical.choice`, and `Quot.sound`.

Still required are the small-$u$ probability-versus-Markov dichotomy, the
large-$u$ order choice and exponential estimate, the double-factorial bridge,
and the cutoff model's Markov/first-moment root inclusion step. Those gaps are
kept explicit and are not replaced by the independent $n^{-1/2}$ critical tail.
