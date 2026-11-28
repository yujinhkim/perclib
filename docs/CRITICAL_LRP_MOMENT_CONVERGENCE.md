# Moment convergence and the chi-square limit law

The package `Analysis/MomentToChiSquare` supplies three independently checked
steps for the I.1.7 route, not an asymptotic estimate for the percolation model.

## The actual moment-to-weak-convergence argument

`SwarmM4.tendsto_chiSq_of_moment_tendsto` takes probability measures on
`[0,∞)` with *every* moment integrable. If all moments converge to the
chi-square moments `(2k-1)!!`, tightness follows from bounded second moments.

For a weak subsequential limit, a further application of the ordinary
second-moment bound at every order bounds the appropriate absolute moments.
Clamping each monomial to a bounded continuous function transfers its moment
into the limit, with a tail estimated by its $2k$-th absolute moment. Moment
determinacy identifies every subsequential limit as the chi-square distribution.
Prokhorov compactness then produces the entire weakly convergent sequence.
There is no blanket uniform bound over all moment orders: convergence of moments
supplies a separate finite constant at each order.

The radius-indexed and raw-measure variants have explicit support conditions.
The `Measure.toProbabilityMeasure` representation preserves the ordinary
integrals and the probability-measure topology; it is not just a type coercion.

## Identification of the paper's limit law

`SwarmM4.Qinf_eq_gammaMeasure` proves
$$Q_{\infty} = \Gamma(1/2,1/2).$$
A weighted normal law supplies the recurrence for the first derivative of the
Gaussian MGF. Leibniz then gives the even moments $(2k-1)!!$, and the same
moment-determinacy theorem identifies the distribution exactly. This makes the
existing chi-square computations and moment-determinacy library usable in the
$Q_{\infty}$ application without silently changing the meaning of $Q_{\infty}$.

`SwarmM4.tendsto_toProbabilityMeasure_Qinf` is precisely the `hconv` interface
used by Proposition I.3.2 and `Analysis/ClusterVolumeTail/I17`: all-order moment
convergence implies convergence of normalized size-biased measures to the
chi-square limit. This is a genuine interface step; it does not discharge
those moment asymptotics or any higher mixed-moment inequality.

## Scope

Full integrability and moment convergence at every positive integer order stay
as explicit inputs, as does nonnegative support. There is no proof here of
I.1.6's moments, no direct volume-tail estimate and no superprocess limit.
These results strengthen and specialize the existing analysis, not its model
non-vacuity.

# Model-level moment convergence and its retained inputs

`Analysis/ClusterVolumeTail/AllOrderMomentsHconv` applies the moment method to
the actual normalized size-biased cutoff volume laws, rather than to a bare
family of probability laws. It defines `I16Model M A` as the paper's all-order
moment ratios in the production `I16rhs` notation, and proves the reindexed
`I16` schema used for size-biased moments.

The moment identity has numerator $E|K|^{k+1}$, the index shift required by
I.1.6, and denominator $(E|K|)(E|K|^2/E|K|)^k$. Normalizing by these factors
cancels both the radius powers and the constants, yielding the chi-square
moments. The model lemmas derive probability and nonnegative support from the
underlying volume law, all-order integrability from `MomentFinite`, positivity
of the first moment from the root's membership in its cluster, and strict
positivity of the size-biased mean.

Consequently `model_tendsto_Qinf_of_I16Model` derives the precise `hconv`
interface. `model_tendsto_tail_I17_of_I16` also derives the I.1.7 conclusions
with the printed coefficient, while retaining almost-sure cluster finiteness
and the restoration estimate explicitly. **What remains unproved is I.1.6
itself**, together with `MomentFinite`; for the tail application, those other
two model inputs remain. There is no claim of canonical moment asymptotics,
joint satisfiability of all hypotheses, or a superprocess limit.

# Case 1: tail-to-median and hydrodynamic consequences

`Analysis/SecondMomentCase1/Hydro` supplies the missing Case-1 direction of the
Corollary I.4.14 assembly. It does not assert the underlying tree-graph tail
itself.

## Exact remaining input

The source's displayed single-cluster bound is represented as
`SingleClusterTail M r m`:
$$P_{\beta_c,r}(|K|\ge n)\le
 \sqrt{2m/n}\,\exp\{-n/(4m^2)\},\qquad n\ge1.$$
The scale $m$ is the actual cutoff first moment in the consumer. The bound is
hands-on input: its tree-growth/exponential-tail derivation is not part of this
package. A separate eventual upper bound on the first moment is also retained.

## Union bound and median estimate

`tail_maxCluster_le` proves
$$P_{\beta_c,r}(|K_{\max}(B_r)|\ge n)
 \le |B_r|\,P_{\beta_c,r}(|K|\ge n).$$
It enumerates the finite window, uses cluster containment inside the doubled
ball around each vertex, and applies the proved translation invariance of the
cutoff law. No larger uncut critical cluster or critical-tail assumption is
introduced.

`mr_le_singleClusterTail` chooses $n=\lceil A m^2\log r\rceil$ and proves an
admissible median threshold at every $r\ge2$ when the scale is at least one.
The exact constant has form $A+1/\log2$, where $A$ is chosen from dimension and
the ball-cardinality constant. Its `exists_ball_ncard_bound` counterpart makes
the normalized-ball bound uniform for every $r\ge2$.

## Hydrodynamic consequence

If $3\alpha<d$ and the single-cluster tail holds at that scale together with
$m(r)\preceq r^\alpha$, `hydro_of_singleClusterTail` proves `Hydro M`. The
improved median estimate bounds the ratio by a constant times
$\log r/r^{(d-3\alpha)/2}$, which tends to zero. The model-specific corollaries
include both big-O and no-ball-hypothesis forms.

This establishes the tail-to-median/core Case-1 reduction. It does not prove
`SingleClusterTail`, the first-moment asymptotic, or Proposition I.4.2, so the
whole corollary is still conditional, as are Cases 2 and 3 with their own inputs.

# Fixed-revealed-set amalgamation for the Gladkov route

`Correlation/Gladkov/Amalgam` proves the deterministic restriction of the
amalgamation lemma used by decision-tree percolation proofs: for a fixed revealed
set $T$, the configurations $C_1\to_T C_2$ and $C_2\to_T C_1$ are independent and
each has the original Bernoulli law.

The underlying model is two independent inhomogeneous Bernoulli copies, packaged
as one `prodBernoulli (twoProfile q)` law on `ι × Bool`. The two projections have
the original law, flipping copies off $T$ preserves it, and events determined by
disjoint coordinate blocks are independent. The flip converts the amalgamated
pair into the raw pair of copies. These steps give `amalgam_indep` and
`map_amalFirst`, with marginal and swap identities needed by their users.

`T = univ` and `T = ∅` give explicit non-degenerate identities: the two
amalgamations are respectively the copied pair and its flip. This is a useful
base case for the general decision-tree induction, not a proof of the inequality.

A random set $S(C_1,C_2)$ made by a decision tree requires additional
measurability/cylindrical invariance and a partition of the proved deterministic
case. The stopping-time Harris, van den Berg/Kahn/Reimer and influence-weighted
Cauchy--Schwarz inputs, plus the DFS combinatorics of Gladkov, are not supplied.
Theorem I.2.7 remains NOT FORMALIZED as a theorem in this repository, despite
this necessary fixed-set lemma being available. No sharpness or optimality claim
is made from numerical side observations.
