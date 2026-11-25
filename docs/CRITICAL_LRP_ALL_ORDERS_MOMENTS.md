# Conditional all-order moment results

These are proof results for the loop-safe Definition I.1.5 cutoff law.  They do **not**
seal either paper root or close `hutchcroft.i.1.5.step.cutoffmoments` as a whole.

## General-`p` upper-bound induction step for Proposition I.4.20

`VolumeMoments/HigherMoments` proves the analytical upper-bound induction step
used in the proof of Proposition I.4.20, for arbitrary `p ≥ 3`. The target is

```text
mom p r ≤ (1+ε) * (2p-3)!! * (mom 2 r / mom 1 r)^(p-1) * mom 1 r
```

eventually for each fixed `ε > 0`, expressed with `momentRatio` and
`mixedMoment`. `middle_sum_eq` supplies the middle double-factorial/binomial
sum; `sum_bound` handles the two endpoint terms and induction products;
`drivingTerm_regularlyVarying` proves index `(2p-1)α`;
`moment_upper_bound` applies the existing Lemma I.4.22 with index gap
`(p-2)α`; and `moment_upper_bound_of_percolation` packages the comparison of
the derivative with the complete driving term. At `p = 3`,
`induction_hypothesis_three` discharges the induction premise itself.

These theorems retain the real percolation hypotheses explicitly: the exact
all-`p` derivative identity, mass transport at the end terms, decorrelation of
the marked expectations, the induction hypothesis for smaller moments, the
first-moment normalisation, and regular variation of `mom 1` and `mom 2` at
indices `α` and `3α`. They do **not** prove those assumptions on the source
model, the second induction needed for two-sided asymptotics, the three
case-specific decorrelation estimates, or Proposition I.4.20 as a whole. The
result is conditional general-`p` ODE assembly, not another scalar ansatz or an
all-order moment-finiteness claim.

### Second induction under asymptotic decorrelation

`VolumeMoments/HigherMoments/SecondInduction` proves the complementary two-sided
step. `normalizedSum_tendsto` applies a positive-weighted-average squeeze to the
normalized binomial sum, using exact endpoint mass transport and induction
asymptotics. `derivative_ratio_tendsto` inserts it into the percolation
derivative identity, with `r c_r |B_r| mom 1 → α`. Lemma I.4.21 then yields the
asymptotic and regular-variation index, while `moment_asymptotic_all` performs
strong induction for all `p ≥ 1` with base identities at `p = 1,2`.

These results use the direct asymptotic decorrelation statement (I.4.20) at
every index. That statement remains an input, along with Lemma I.4.1, mass
transport, first-moment normalization and regular variation of the first two
moments. The error-only alternative (I.4.21) and the three case-specific proofs
of decorrelation are not supplied here. Therefore the percolation model's
all-order moment asymptotics are still not established, although the complete
analytic second-induction mechanism is now available once those inputs are
proved.

## All-order stochastic comparison

`MomentMonotonicity/MomentTransfer.lean` proves that if `π e ≤ κ e` at each edge and
`F` is measurable and inclusion-monotone, then
`∫⁻ F d(edgeMeasure π) ≤ ∫⁻ F d(edgeMeasure κ)`.
The proof uses the common threshold-mark coupling, so it applies to all measurable
increasing functionals, not just indicators of increasing events.

Consequently the laws now transport for every natural `q`, every real exponent
`p ≥ 0`, and, for the allowed cutoff profile, the reduced-parameter uncut law:

`cutoff_lintegral_clusterVol_pow_ne_top` bounds a cutoff `q`-moment by the same
moment at `β(1 − K r/K 1)`.  *The dominating finite-moment premise remains explicit.*
No uncut first moment, higher-moment bound, or lattice sharpness result is
manufactured by this comparison.

## Exact window content

`MomentMonotonicity/WindowMoments.lean` identifies each positive cluster moment with
the supremum of its moments inside a cofinal increasing family of finite windows.
Each individual window moment is bounded by the finite cardinal power of the
window.  A full moment is finite exactly when those window moments are uniformly
bounded.  Furthermore, the special hypothesis that the cluster is a.s. contained
in one fixed finite set gives the corresponding bound all at once.

These lemmas **must not be confused with a finite-support proof of the all-moment
cutoff law**.  Bounded edge lengths alone do not bound the whole cluster, even
though they give a finite potential-degree bound.  A range-limited percolation
graph may have an infinite connected component.  In particular, `J_r` is not being
replaced by a finite-box probability law.

The implementation instantiates the characterization at `P_{β,r}` and at the
paper-model `SourceModelData.cutMoment`.  Raw lattice-box cardinalities are
`(2n+1)^d`; a real-radius closed sup-norm ball has `(2⌊r⌋+1)^d` points.  These are
not silently replaced by a normalized-to-one factor.

## Tauberian endpoint

`Analysis/NormalizedAEndpoint.lean` proves `a ≥ 1` from the source's two moment
asymptotics and Jensen's inequality on `[0,∞)`.  The second asymptotic is explicitly
converted from `φ/f → A2` to `φ/(A2 f) → 1`, preserving eventual nonvanishing.

This endpoint needs the actual probability laws, their finite first and second
moments, and positive means.  It does not create the `A3` convergence or
positivity, the uniform ghost comparison, a Tauberian proof, or either paper root.

## Remaining requirements

To obtain every finite cutoff moment one still needs a suitable subcritical first
moment and a higher-order tree-graph bound: precisely the uniformity identified by
`powMoment_ne_top_iff_uniform_window`.  The second- and third-moment results are
special cases; the other orders are not inferred from support finiteness alone.

## Intensity monotonicity at fixed cutoff

`MomentMonotonicity/CutoffParameterMonotonicity.lean` proves, for
`β ≤ γ`, `E_{β,r}|K|^q ≤ E_{γ,r}|K|^q` for every natural `q`.
Its `cutoff_fourthMoment_mono_beta` specialization is the fixed-cutoff
fourth-moment comparison needed in the `i.4.g7` application. It is proved from
edge-probability and mark-coupling monotonicity, with no sharpness or
finite-moment hypothesis. The next module supplies the separate cutoff-to-uncut
comparison.

## All-order limit in the cutoff radius

`MomentMonotonicity/CutoffMomentConvergence.lean` proves
`clusterVol_atParameter_eq_iSup`: under an increasing pointwise-convergent family
of edge probabilities, cluster volumes on the common mark space are suprema of
their finite-stage values.  Finite-path exhaustion, not a finite-cluster or
finite-moment assumption, supplies this identity.  Integrating natural powers
with `ENNReal.iSup_pow` and `lintegral_iSup` yields, for every natural `q`,

```text
sup_{r : ℝ} E_{β,r}|K_o|^q = E_β|K_o|^q,
lim_{r→∞} E_{β,r}|K_o|^q = E_β|K_o|^q.
```

These equalities hold in `ℝ≥0∞`, including value `⊤`.  The module also proves
monotonicity in the cutoff radius, the fixed-radius uncut bound, and transfer of
an explicit finite uniform-in-radius bound to the uncut moment.  It does not
construct that uniform bound and does not infer any moment from a lower order.

The accepted `MomentMonotonicity/SourceModelCutoffLimit.lean` supplies the same
limit at the genuine `SourceModelData`, not only the raw sup-norm kernel.  Its
`SourceModelData.tendsto_K_atTop_zero` derives the profile tail from
`K_eq_integral` and the normalization error, without assuming it.  The
`cutRadialSym` engine is valid at arbitrary source norms (including the flat
counterexample), and `SourceModelData.iSup_cutMoment_eq` and
`SourceModelData.tendsto_cutMoment` give every natural `M.cutMoment` as an
extended-real supremum/limit at `M.betaCrit`.  This still proves no moment
finiteness in this convergence theorem.  The separate
`MomentMonotonicity/StrictCutoffEpsilon.lean` now proves the strict domination
at arbitrary normalized source norms, but likewise derives no finite-moment or
uniform-moment bound.

`MomentMonotonicity/SourceModelMoments.lean` gives the complete comparison record
at `SourceModelData`, including an arbitrary admissible norm: for `β ≤ γ`, both
increasing-measurable-event comparisons, every natural-moment comparison, and
both two-point comparisons.  It uses `cutoffProfile_le` and the common coupling,
not the sup-norm-specific coefficient `K r/K 1`.
`hutchcroft.i.4.g7` is now mapped to
`PercLib.CriticalLRP.Orchestration.SourceModelData.cutoff_mono_beta_and_le_uncut`.
The raw sup-norm module separately checks a term-level power-law fourth-moment
application after converting `Percolation.cardFun` to `clusterVol`.  A concrete
inhabitant of `SourceModelData` and the flat-norm coefficient counterexample are
in `Orchestration/SourceModelNonvacuity.lean`.

This closes `i.4.g7` as a *comparison step*, not uncut Theorem I.2.13, cutoff
moment finiteness, the sharpness asymptotic behind `i.4.g6`, or either paper
root.

## Renewal prerequisites, not an all-moment proof

`CountableProduct/Renewal.lean` proves the deterministic bound from
`cluster_subset_renewal`, expressing the cluster by the root and clusters after
removing all root-incident edges.  Its `encard_cluster_le_offspring` records the
bound as at most one plus a sum of open-neighbour pruned clusters, with no finite
support or finite-cluster hypothesis.  The helper definitions are in
`CountableProduct/Renewal/Defs.lean`.

The same file proves `lintegral_indicator_mul_of_sdiff_determined`: for any
measurable extended-real `G` independent of one coordinate by explicit deletion,
the expectation of the coordinate indicator against `G` factors by that edge's
probability.  These are inputs to a proposed high-temperature row-sum recursion;
they do not yet prove its all-order induction, a finite fourth moment, or the
critical tree-graph inequality.

## Compiled renewal prerequisites and the remaining contraction gap

Accepted submission `smwp81k72` adds
`CountableProduct/MomentRecursion.lean`, its helper definitions in
`MomentRecursion/Defs.lean`, and `CountableProduct/SetEncCard.lean`.  These are
infrastructure, not a higher-moment theorem:

* `measurable_prunedVol` proves measurability of the cluster volume after all
  edges incident to the root are closed; `measurable_encard_of_measurable`
  generalizes this to the cardinality of a measurable set-valued map on a
  countable type.
* `lintegral_prod_indicator_mul_of_sdiff_determined` factors a product of edge
  indicators on a finite set against a measurable functional fixed by deleting
  precisely those edges.  Its independence hypothesis is explicit and is not
  an assertion about arbitrary overlapping pruned clusters.
* `lintegral_offspring_eq` computes the first moment of the one-step renewal
  offspring sum.  Under a uniform off-diagonal intensity row-sum bound `m < 1`,
  `lintegral_offspring_le` bounds it by `m(1-m)⁻¹` and
  `lintegral_offspring_ne_top` proves finiteness, without translation
  invariance or a finite-range assumption.
* `lintegral_cluster_pow_le_sum` bounds the `k`-th cluster moment by the
  binomial sum of moments of the offspring sum, including the order-`k` term.
  This does not provide a coefficient below one or a finiteness induction.

`offspring_second_moment_exceeds_row_sum` records a concrete obstruction to a
naive contraction from row sums and marginal moment bounds alone.  The open
obligation `hutchcroft.i.1.5.step.cutoffmoments` therefore remains open: no
first-hit partition, branching-process coupling, uniform higher-moment
estimate, or critical cutoff-moment finiteness is asserted by these modules.

### Rejected first-hit correction

Independent review `smwp9xgrt` checked and refuted the proposed first-hit repair
in the earlier `smwp81k72` report; this is not an accepted route.  On the
three-vertex complete graph with root `0`, make `{0,2}` and `{1,2}` open and
`{0,1}` closed, and give `1` priority over `2`.  The root cluster has three
vertices.  After closing the root edges, both neighbour clusters are `{1,2}`.
The priority-first piece belongs to the *closed* neighbour `1`, the piece at `2`
is empty, and the open-edge-weighted sum is zero rather than `|K_0|-1 = 2`.
`full_sum_identity_fails` formalizes this using the repository's `cluster`,
`blockT`, and `Config`; even `|K_0|-1 ≤ Σ_y B_y|Ã_y|` is false.

The unweighted pieces do form a finite-set partition.  The checked general
formula is instead
`Σ_y B_y|Ã_y| = |K_o|-1 - Σ_y (1-B_y)|Ã_y|`.  Selecting priority only among
*open* neighbours would avoid this loss but reintroduce the root-edge
dependence needed by the failed factorization.  Literal `Ã_y` blindness also
fails, although its open-weighted summand can be rewritten using a blind core;
that repair does not restore coverage.  These declarations are in
`.ultramath/smwp9xgrt/m1/{Counterexample,General,Blindness}.lean`, independently
recompiled with warnings as errors and audited to use only the three standard
axioms.  They are a counterexample to the proposed recursion, not to
subcritical all-order moment finiteness, and are not imported as a paper lemma.

## Exploration-envelope ingredients, not a cluster theorem

Accepted partial submission `smwp9xgrt` supplies
`Probability/Exploration/Envelope/Defs.lean`, `Envelope.lean`, `PGF.lean`,
and `MomentBound.lean`, in namespace `PercLib.Probability.ExplorationEnvelope`.
`UniformRowSum` formulates a uniform bound on every finite partial row sum;
for nonnegative weights this agrees with the extended nonnegative total sum.
These declarations are not yet instantiated on the long-range law.

The finite PGF modules compute the tilted weight of the number of open edges
among an arbitrary finite edge set:
`sum_tiltedWeight_eq_prod = ∏e∈S, (1 + p e (t-1))`.
For nonnegative `p` and `t ≥ 1`, `sum_tiltedWeight_le_exp` bounds this by
`exp ((t-1)m)` whenever the relevant finite intensity sum is at most `m`.
This is an exact finite-configuration calculation, not an assertion that the
corresponding infinite cluster is supported on a finite set.

The scalar recursion is `u₀ = 1`,
`u_(n+1) = exp (m(λu_n-1))`.  `envelope_le_inv_mul` bounds it by `1/(mλ)` for
`0<m≤1`, `λ≥1` and `mλ≤exp(m-1)`; `exists_admissible_lambda` proves that a
nontrivial `λ>1` exists for `0<m<1`.
`pow_le_factorial_div_log_mul_rpow` proves the pointwise estimate
`x^k ≤ (k!/(log λ)^k) λ^x` for `x≥0`, and
`exists_lambda_and_moment_bound` packages the resulting scalar constants.
It needs a separately established exponential cluster-moment bound; it does
not produce one.

The frontier-exploration proof outline in `.ultramath/smwp9xgrt/m2/PROOF.md`
uses only conditional independence of unrevealed coordinates, not independence
of overlapping branches.  The countable generation state and cluster
exhaustion, the BFS specialization of the history interface, finite-horizon
conditional estimates, and their final monotone limit remain substantive
obligations.  No exponential or all-order infinite-cluster theorem,
high-temperature cutoff application, or critical source-moment finiteness is
claimed by these modules.

### Adapted revelation at the actual product law

Accepted submission `smwpalb9h` adds
`Probability/Exploration/AdaptedReveal/{Defs,Reveal,PGF}.lean`, in namespace
`PercLib.Probability.AdaptedReveal`.  `RevealData ι St` fixes a countable state
space, the revealed coordinate block for each state, and the explicit `fiber`
hypothesis that the state fibre is a measurable cylinder on precisely that
block.  This is a genuine stopping-set interface, not an unsupported assertion
that every stopping time or BFS automatically satisfies it.

`lintegral_prod_coord` factorizes finite products of one-coordinate measurable
functions under the repository's `prodBernoulli`.  The generated coordinate
sigma-algebras make the history measurable even when the revealed block is
infinite.  Consequently `lintegral_adapted_prod` gives, for any history
observable `G` and finite fresh set `S σ` disjoint from each state's revealed
block,

`∫⁻ G ∏_{e∈S(state)} f_e(e open) =
  ∑' σ, (∫⁻_{state=σ} G) ∏_{e∈Sσ} ∫⁻ f_e(e open)`.

`lintegral_adapted_pgf` specializes this to `t ^ openCount`, with exact
Bernoulli factors `t p_e + (1-p_e)`.  `lintegral_adapted_pgf_le` takes a
statewise upper bound `B σ` on those products as its explicit hypothesis.

The random revealed set need not be finite, but only the finite fresh set is
bounded by the product calculation.  This is general probability
infrastructure; it does not by itself identify a particular exploration or an
infinite-cluster limit.

### Deterministic BFS, countable adapted histories and the cluster limit

The second accepted part of `smwpalb9h` adds
`CriticalLRP/Exploration/BFS.lean` through the `BFS/` modules, in namespace
`PercLib.CriticalLRP.Exploration.BFS`.  Starting from the actual `Config V` and
`cluster`, `A ω o k` is the current frontier, `P ω o k` the processed set,
`U ω o k` the undiscovered set, and `gen ω o k = A ω o (k+1)`.
The finite-horizon set is `horizon = P ∪ A`; none of these sets is assumed
finite.

The modules prove the partition and disjoint-generation formulas,
`cluster_eq_iUnion_A` and `cluster_eq_insert_iUnion_gen`, and
`gen_encard_le_queried`: different newly discovered vertices carry different
open queried edges.  `disjoint_revealed_queried` states that the current query
is fresh, while `state_eq_of_eqOn_seen` and `_revealed` prove deterministic
stopping-set dependence even if the revealed edge set is infinite.
`disjoint_seen_queried` and `disjoint_queried` separate queries at distinct
steps.  Under countability of `V`, all required state, query, horizon and
cluster events are measurable.

For counting, `encard_horizon` is `1 + Σ_{j<k}|gen j|`, and
`encard_cluster_toENNReal_eq_tsum` is the exact infinite-cluster identity
`|K_o| = 1 + ∑'j |gen j|` in `ℝ≥0∞`.  `tendsto_encard_horizon` gives finite-
horizon convergence.  The extended power `epow lam` takes the supremum of finite
powers, is the usual real power on finite extended naturals, and is `⊤` at `⊤`
for `lam > 1`.  It commutes with suprema (`epow_iSup`), so
`lintegral_epow_encard_cluster_eq_iSup` gives the infinite-cluster extended
moment as the supremum of finite-horizon extended moments, without requiring a
finite-cluster hypothesis.

`FinState V = Option (Finset V × Finset V)` is a genuinely countable refinement:
it records the processed set and frontier when both are finite and `none`
otherwise.  `finRevealData` proves the BFS `fiber` condition for this state;
`revealFin none = univ` forces a fresh set at `none` to be empty.
`lintegral_bfs_adapted_prod`, `_pgf`, and `_pgf_le` then instantiate the
accepted product-law factorization.  This handles the history interface, not
the a.s. finiteness of the frontier.

The next PGF section supplies the one-step envelope arithmetic.  The remaining
step is to insert it into a finite-frontier generation induction and then use
the finite-horizon limit.  No exponential or all-order cluster moment is
claimed by the BFS decomposition or by the extended-power limit alone.

### Poisson PGF bound throughout the queried set

Accepted submission `smwpbvro2` adds
`CriticalLRP/Exploration/BFS/Poisson/`.  The scalar factor identity proves
`t*p+(1-p)=1+p*(t-1)` for finite `t ≥ 1` and `p ≤ 1`, with the two truncated
subtractions controlled explicitly.  `prod_pgfFactor_le_exp` and its
`unitInterval` version then use the committed exact tilted-weight calculation
to bound a finite product by `ofReal (exp ((t-1)m))`.

`UniformRowBound p M` is the uniform real row-sum condition over all finite
partial sums not containing the root; `uniformRowBound_of_tsum_ennreal` supplies
the honest `ℝ≥0∞`-tsum version.  No use is made of the junk-valued real `tsum`
of a non-summable family.  `sum_le_card_mul_of_subset_edgeSet` charges a finite
fresh edge set once per frontier vertex, with budget `|T|·M`, not `|T|²·M`.

At the BFS state, `freshEdgeSet` is disjoint from its revealed block by
construction and agrees with the actual queried set on every reachable `some`
fibre.  `lintegral_bfs_adapted_pgf_le_rowBound` bounds finite fresh subsets.
The directed-exhaustion result `lintegral_bfs_epow_le_rowBound'` then bounds

`∫⁻ G · epow t (|freshEdgeSet(state) ∩ ω|)`

by the history sum with the same row budget at every finite exhaustion stage.
The exhaustion is constructed from countability of the edge type, so no finite
frontier, finite degree or finite queried set is assumed in this full-fresh
result.  History measurability is proved by the accepted `measurable_history`;
`FinState.none` contributes a vacuous fresh count rather than being silently
dropped.

`ofReal_exp_card_mul` writes the budget as a per-vertex power, and
`lintegral_bfs_epow_envelopeStep` identifies that power with
`envelopeStep m λ u ^ |T|`, exactly the scalar envelope recursion.
For the **true** generation, `lintegral_bfs_epow_gen_le_rowBound` and
`lintegral_bfs_epow_gen_envelopeStep` apply `gen_encard_le_queried` on `some`
fibres, but retain the explicit premise
`∀ᵐ ω, finState ω o k ≠ none`.  They do not prove almost-sure frontier
finiteness or insert this estimate into a generation induction.
Non-vacuity checks cover a zero intensity with any `0 ≤ M` and the `p=1`
coordinate factor.  These are not lattice critical-parameter instantiations.

### History functions and the finite-state induction step

The second accepted part of `smwpbvro2`, now under
`CriticalLRP/Exploration/BFS/Generation/`, gives an alternative per-fibre one-step
form directly suited to induction.  `RowSum` is another finite-partial-sum real
row bound, bridged at integration to the same row-charging geometry.
`hist o k ω` is the actual configuration intersection with the state's revealed
block, and `IsHistFun` records a measurable function of that block.
`IsHistFun.succ` is proved using the explicit map `histShift`, the monotonicity
of revealed blocks, and `finState_hist_eq`: history functions remain valid at
the next BFS step, rather than being assumed to be arbitrary future functions.

`epow_add_le`, `epow_mul_le`, and `epow_ofReal_pow` are the scalar inequalities
needed to combine the current generation with the remaining horizon.  The
finite-fresh supremum is established without assuming the queried set is finite.

For a reachable state `some (Q,T)` (with `Q` and `T` disjoint) and measurable
history function `H`, `fibre_step` proves the exact finite-state estimate:

`∫_{finState=some(Q,T)} H(hist) · epow τ |gen| ≤
  (∫_{finState=some(Q,T)} H(hist)) · exp((τ-1)m|T|)`.

Its proof applies adapted revelation to a single supported history and then
passes to the directed supremum over all finite fresh subsets.
`stateBound_some_eq_epow` expresses the right side as an envelope power;
`stateBound_none = ⊤` records that no information is available on an infinite
state there, while unreachably non-disjoint finite states must be shown to have
zero fibre measure during global assembly.

Still open is the sum over all `FinState` fibres, treatment of unreachable and
`none` fibres, and the genuine induction over remaining generations using
`IsHistFun.succ`.  Only after these are proved can the envelope bound and BFS
finite-horizon limit give an exponential cluster moment.  No such moment is
asserted yet.

## Completed generic high-temperature cluster moments

Accepted full solution `smwpdapl6` completes the preceding programme under
`CriticalLRP/Exploration/BFS/HighTemperature/`.  A Borel–Cantelli local
finiteness theorem from the row bound proves `ae_finState_ne_none` at every
fixed horizon, so the `none` fibre of the earlier one-step estimate is null.
`isHistFun_fibreData` produces all required statewise history data without a
new hypothesis.  `gen_moment_induction` then proves the remaining-generation
bound for every actual `IsHistFun`, using the accepted one-step estimate,
`epow_add_le`, `epow_mul_le`, and the null-fibre-aware state sum.

At the root this gives `lintegral_epow_horizon_le`, and the committed
monotone-limit argument gives the genuine infinite-cluster bound.  For
independent Bernoulli edges on any countable `V`, a real uniform off-diagonal
row bound `UniformRowBound p m`, `0<m≤1`, `1≤λ`, and
`mλ≤exp(m-1)` imply

`∫⁻ ω, epow (ofReal λ) ((cluster ω o).encard) ≤ ofReal (1/m)`.

`exists_lam_lintegral_epow_encard_cluster_le` supplies an admissible `λ>1`
when `0<m<1`; `m=0` has a separate bound.  Moreover,
`lintegral_pow_encard_cluster_le_inv_mul` gives the explicit natural-moment
bound for every `k`, and `exists_lam_lintegral_pow_encard_cluster_le` supplies
the admissible parameter.  The natural-moment proof derives almost-sure cluster
finiteness from the extended exponential bound before using `encard.toNat`.

Thus the generic high-temperature statement is now an actual formalized
infinite-volume result, not a finite-window substitute.  The deferred
`hutchcroft.i.1.5.step.cutoffmoments` obligation nevertheless remains open:
it concerns finite cutoff radii at `β_c`, whose row sums at the reduced
parameter have not been shown to satisfy this high-temperature hypothesis.
No source-model instantiation, `betaCrit` threshold, sharpness theorem, or
paper root is claimed by the generic result.

### Raw power-law high-temperature corollary

`CriticalLRP/IntensityMoments.lean` applies the generic theorem to the existing
power-law first-moment interval. If `J s(x,y) = ‖y-x‖∞^(-s)` in the
`Real.toNNReal` intensity presentation on `Fin d → ℤ`, with `s>d` and
`βM < 1`, then `power_lintegral_clusterVol_pow_ne_top` proves
`∫⁻ (clusterVol ω x)^k ∂(law (intensityProfile J β)) ≠ ⊤`
for every root `x` and every natural `k`. The row-sum/law bridge is explicit,
and finite-cluster conversion is derived from the exponential bound before
using the natural-power normalization. This is an actual all-moment result on
the infinite lattice at an explicit high-temperature parameter, not merely a
generator of abstract inequalities.

### Canonical `lrKernel` and all-order cutoff

`PowerLawHighTemp/Moments.lean` carries the same high-temperature conclusions to
the paper-literal `lrKernel d α`. Its
`lrKernel_lintegral_clusterVol_pow_ne_top` proves all natural cluster moments at
every vertex under `β M < 1`, and its interval form gives `β < (M+1)⁻¹` with
all moments finite at every root. `k = 1` recovers the earlier first-moment
statement exactly.

It also proves `modelProfile_cutoff_lintegral_clusterVol_pow_ne_top`: every
natural cluster-volume moment is finite at every root for the loop-safe cutoff
`cutoffSymKernel (modelProfile d α) d r`, for every radius `r : ℝ`, under the
same condition `β M < 1`. The positive-interval theorem chooses a single
`β₀ = (M+1)⁻¹` independent of `r`, hence the radius-uniform all-order cutoff
region. The proof uses domination by the uncut law at the *same* parameter,
not reduced-parameter sharpness or a finite-window approximation. In
particular, `hutchcroft.i.1.5.step.cutoffmoments` at `β_c` remains open.
