# Second cutoff moment: native RHS algebra and analytic inputs

`Analysis/Cutoff/SecondMoment` is the consolidated version of the useful components
from swarm `smwv94uce`.  It advances Lemma I.4.1 from $p=1$ to $p=2$ only:
the real translated source cutoff on the infinite lattice is used throughout,
with the closed source ball $B_r=\{y:M.S.\rho(\mathrm{toVec}\,y)\le r\}$.
A torus, a graph-specific substitute, or a finite box is not substituted for this object.

## Proved at $p=2$

The definition layer gives the two genuine excluded masses:

- `exclMassQuad r = E[|K| sum_{y in B_r,y notin K}|K_y|^2]`;
- `exclMassSqLin r = E[|K|^2 sum_{y in B_r,y notin K}|K_y|]`,

together with their strict-ball and shell variants, and
`p2RHS r = exclMassQuad r + 2 * exclMassSqLin r`.
The coefficient is exactly $\binom21=2$, not an arbitrary free exponent.
`p2SourceSum` names the source's displayed indexed sum without changing its shape.

`Binomial.lean` proves that the general-$p$ source-model mass-transport bridge
`PivotFlux.lintegral_paperSumP_eq_rooted` collapses to those two masses when $p=2$.
In particular `lintegral_paperSumP_two_eq_of_cutMass` proves
`∫⁻ ω, PivotFlux.paperSumP M 2 r ω ∂M.cutLaw r = p2RHS M r`
under the explicit finite-first-moment assumption `M.cutMassAt r 0 ≠ ⊤`.
The source binomial coefficient is derived, and the closed/strict/shell identity
`p2RHS r = p2RHSStrict r + p2RHSShell r` is exact in `ℝ≥0∞`.

## Finiteness and majorants

`Finiteness.lean` proves translation-independence of every vertex cluster moment:
`lintegral_clusterVol_pow_vertex`.
Consequently the finite closed-ball sum of the $p$-th volumes has moment
`((M.ball r).ncard : ℝ≥0∞) * M.cutMoment p r`.
These are identities at vertices of the actual infinite lattice, obtained by mapping the
cutoff law by shifts, not assertions about a proxy graph.

For either excluded mass $Q$ (quadratic or squared-root linear) the crude pointwise
estimate $xy\le x^2+y^2$ gives
$$
  Q(r)\le |B_r|(M.cutMoment 2 r+M.cutMoment 4 r).
$$
Thus
$$
  M.p2RHS r\le3|B_r|(M_2+M_4)\le6|B_r|M_4
   \le90|B_r|M_1^7,
$$
where the last comparison requires $c>0$, positivity of $r$, and
$\forall z,\rho(\mathrm{toVec}\,z)=c\,\mathrm{linfNorm}(z)$; it consumes the landed
fourth-moment transfer.  `p2RhsMass_ne_top` proves that `p2RHS` is finite under those
hypotheses plus `M.cutMoment 1 r ≠ ⊤`.  Both have explicit scaled-linf-norm and
source-witness instantiations (`c=2`).  These hypotheses are not discharged by this package.

`Corner.lean` and `ShellPos.lean` give the exact real discrepancy
$$
  \mathrm{rhsScalarTwo}(r)-\mathrm{rhsScalarTwoStrict}(r)
   =\mathrm{coeffRHS}(r)(M.p2RHSShell r).toReal,
$$
assuming finiteness of the strict and shell masses.  At a positive nonempty shell,
the layers are nonzero because their integrands dominate the landed $p=1$ shell integrand
via $|K_y|\le|K_y|^2$ and $|K|\le|K|^2$.  Hence a nonzero scalar coefficient gives a
genuine closed/strict distinction.  No two-sided formula at an attained radius is inferred.

## Radius regularity, distinct from the formula

`RadiusMoments.lean` proves, when the moment at the top of a finite window is finite,
that `cutMomentReal p` is monotone there, differentiable almost everywhere, and has
nonnegative derivative.  It proves that the attained-radius set is Lebesgue-null on
the entire halfline and upgrades a pointwise off-corner derivative formula into an
almost-everywhere one.  The $p=2$ radius-integral and absolute-continuity wrappers
retain the finite endpoint moment, off-corner differentiability, and majorant `g`;
only the corner-finiteness side condition is discharged independently.

## Quadratic flip calculus, capped domination and FTC

`RussoInf/QuadraticFlux.lean` proves the flip product rule, its closed-configuration
form and its square specialization.  The exact identity
$$
  \Delta(g^2)=2g_{\mathrm{off}}\Delta g+(\Delta g)^2
$$
comes with the local bound `abs_flipDiff_sq_le_touch` by `8 m^2` for `|g|≤m`,
the corresponding pivotal-flux bound, and the transfer of a summable touching-probability
series to the square.  Exact pivotal-flux decomposition into bilinear and diagonal terms
uses separate integrability assumptions where needed.  `RussoInf/MergeSubset.lean` gives
only the forward union-of-clusters inclusion, not the reverse equality or radius interchange.

`QuadraticMoments/Defs.lean` and `Main.lean`, in namespace `CappedMoments`, cap the
cluster volume in `ℝ≥0∞` before converting to `ℝ`.  For `0 ≤ N`, the exact capped-square
flip difference has absolute value at most `2 N` times the capped linear increment.
That lifts to pivotal flux and the quadratic series comparison, with all integrability
and first-moment-summability inputs visible.  The real cap agrees with the square on a
finite event that satisfies the cap; removal as `N→∞` is not assumed.

`ExcludedFluxL1.lean` proves the exact closed-coordinate factorization for a measurable observation
integrable under both single-coordinate pinned laws. The open- and closed-pinned expectations are
explicit inputs; this requires no separate case for parameter $0$ or $1$. Instantiating it for the
squared full cluster volume still requires discharging those pinned-law integrability hypotheses,
and removing the truncation from the real pivotal flux is separate work.

`SecondMoment/FTC.lean` converts an integrated identity for `rhsScalarTwo` into the
same pointwise derivative at every point where `rhsScalarTwo` is continuous.  Conversely,
a pointwise derivative at every interior point gives the integrated identity after the
usual continuity and interval-integrability hypotheses.  It also gives the exact
increment bound by `∫ |rhsScalarTwo|` and a `C`-Lipschitz estimate when
`0 ≤ rhsScalarTwo ≤ C`.  These are true analytic implications, not assertions that the
primitive identity or continuity is already available.

`Cutoff/WindowRemainder.lean` supplies the exact kernel-profile shift
`cutoffProfile K r′ s − cutoffProfile K r s = K r − K r′` on every edge of a radius
window.  The closed-edge probability consequently has a single multiplicative factor,
and its increment has remainder bounded uniformly by a quadratic scalar in that shift.
For a finite vertex set `S`, the sum `T` of closed-edge weights satisfies
`|T(r′) − T(r) + x T(r)| ≤ x² · card S`, with `x = β_c (K r − K r′)`.
This is the genuine law-level first-order estimate a quadratic exchange must consume,
not proof that the exchange holds.

`RussoInf/Merge.lean` closes the single-edge merge gap itself.  A walk either takes an
old edge and stays in its current cluster, or takes the new edge and reaches one of
its endpoints.  Keeping all three clusters through a last-step induction gives the reverse
inclusion; combined with `MergeSubset.cluster_union_edge_subset` this yields the exact
identity `cluster (ω ∪ {s(x,y)}) o = cluster ω o ∪ cluster ω y` for `x ≠ y` and `x ∈ cluster ω o`.
There are explicit `forceOn` forms for both `e ∈ ω` and `e ∉ ω`.

When `y ∉ cluster ω o`, the edge is proved closed and the two clusters are disjoint, so
`clusterVol (ω ∪ {s(x,y)}) o = clusterVol ω o + clusterVol ω y`, an identity of extended
cardinalities with no finite-box restriction.  `flipDiff_clusterVol_sq_eq` gives the exact
real flip difference `2 |K_o| |K_y| + |K_y|^2` when the two volumes are finite;
`flipDiff_clusterVol_sq_eq_cases` computes all four endpoint cases and proves that the other
regions are not wrongly assigned a zero increment.

`SecondMoment/Regularity/Defs.lean` introduces three marked window masses
`quadPairMass`, `sqLinPairMass` and `connCubeMass`.  Cluster coincidence on
`{y ∈ K_0}` gives the exact identities `quadPairMass = connCubeMass + exclMassQuad`
and `sqLinPairMass = connCubeMass + exclMassSqLin`, hence
`p2RHS + 3 * connCubeMass = quadPairMass + 2 * sqLinPairMass`.
All three are monotone in the radius, and the common cubic mass is at most `cutMoment 4`.
This removes the antilinearity issue of the excluded indicator without any inequality loss.

`SecondMoment/Regularity/Main.lean` supplies frozen-cluster equality off the box-change and
escape events, reusable box/escape integral vanishing, and a DCT increment skeleton for
marked window masses.  It proves `tendsto_p2RHS_toReal_nhdsGT` from a finite fourth cutoff
moment at a strictly larger radius: the actual source $p=2$ excluded RHS is **right continuous**
at every positive radius.  At an attained radius this has the closed-window value.
`rhsScalarTwo` inherits this once `coeffRHS` is continuous.

`SecondMoment/Regularity/Left` proves the strict-window left limit
`Tendsto (fun r => (M.p2RHS r).toReal) (𝓝[<] r₀) (𝓝 ((M.p2RHSStrict r₀).toReal))`
from a finite fourth moment at $r_0$. It uses monotone convergence of the three marked masses,
not a replacement of the closed window by its value at an attained radius. Off a sphere, the
strict and closed windows coincide, so `continuousAt_p2RHS_toReal_of_no_sphere` and
`continuousAt_rhsScalarTwo_of_no_sphere` give two-sided continuity, the latter assuming
continuity of `coeffRHS`. At a positive shell the limit is proved not to be the closed-window
value; no attained-radius two-sided derivative is claimed.

## Closed-edge quadratic truncation

`Fibre/QuadraticClosed` proves the finite-truncation square flip and its closed-coordinate
factorization, using boundedness only to justify the latter. It then proves monotone convergence of
the truncated excluded increments to `qPairIncrFull` and `qEdgeIncrFull`. Consequently
`iSup_ofReal_one_sub_mul_pivotalFlux_sq_eq_lintegral_qEdgeIncrFull` removes the finite truncation
on the $\mathbb R_{\ge0}\cup\{\infty\}$ side at a fixed radius. The real-valued perimeter is only
a bounded inequality under an explicitly finite full-cluster integral, not a full untruncated
pivotal-flux identity. No infinite cluster cardinality is silently converted to zero, and no
radius derivative is obtained here.

## Unordered edges and the vertex-side expectation

`SecondMoment/EdgeFamily` makes the edge count explicit. A nondegenerate unordered edge is counted
by its two ordered endpoint pairs; the diagonal carries zero weight. This proves the unconditional
$\mathbb R_{\ge0}\cup\{\infty\}$ identity
`∑' e, quadEdgeWeight = ∑' b, ∑' c, quadPairWeight`. Cofinality uses `B ↦ B.sym2`, not an
additivity or summability assumption. On configurations with finite cluster volumes, the oriented
weight is exactly the source's binomial weight. `lintegral_tsum_quadEdgeWeight_eq_p2RHS` consequently
identifies the expectation of the full unordered edge family with `p2RHS`, using a finite first
cutoff moment to obtain a.e.-finite clusters. These are the edge weights consumed by `Flux`.

## Coupled mass transport at $p=2$

`SecondMoment/Transport` proves the unconditional infinite-volume identity
`PivotFlux.lintegral_p2PaperSum_eq_p2RHS` in $\mathbb R_{\ge0}\cup\{\infty\}$:
the paper's pivot-pair double sum with summand $2|K_0||K_y|+|K_y|^2$ integrates to
`exclMassQuad + 2 * exclMassSqLin`. The diagonal term transports `|K_y|^2`; the cross term
transports the coupled pair `(|K_a|, pivotWeight a b c)`, not merely its second factor.
At the root, the identity $\sum_{a\in K_0}|K_a|=|K_0|^2$ gives the required squared-root
factor. `Transport/Edge.lean` also writes the finite-cluster single-edge flip increment as
the sum of its two oriented pair weights.

`Transport/ToReal.lean` supplies simultaneous a.e.-finite cluster volumes from a finite first
cutoff moment. When `p2RHS` is finite it proves `Integrable` of the real paper sum and identifies
its integral with `(p2RHS).toReal`; `Transport/Coeff.lean` factors `cutEdgeDeriv` as
`coeffRHS * cutEdgeClosedWeight`. These real-space and coefficient steps do **not** by themselves
prove the real per-edge FLUX identity or a radius derivative.

This is the vertex-side expectation identity of the proof of Lemma I.4.1. It is used by the flux
assembly, but is not itself a radius derivative.

## Fixed-radius real quadratic flux

`SecondMoment/Flux/PerEdge.lean` writes the flip difference of the untruncated square as the real
quadratic edge weight evaluated on the **closed** configuration. This uses the exact merge
identity in $\mathbb R_{\ge0}\cup\{\infty\}$, so no infinite opened-cluster value is lost through
`toReal`. The nonnegative closed-coordinate factorization then gives
`cutEdgeClosedWeight * pivotalFlux(|K_0|^2) = E[(quadEdgeWeight).toReal]` under a finite first
cutoff moment. The square flip difference is proved genuinely integrable from finite `p2RHS`;
the identity is not vacuous through Lean's zero integral of a nonintegrable function.

`SecondMoment/Flux/Main.lean` applies Tonelli to the extended-nonnegative edge family and finite
per-edge expectations. It proves `tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo`: the infinite
edge sum is $M.coeffRHS(r)(M.p2RHS(r)).toReal$ at a fixed radius, with finite first cutoff moment
and finite `p2RHS` visible as hypotheses. A wrapper derives the latter finiteness from the
scaled-norm boundedness and first-moment inputs used by `SecondMoment/Finiteness`.

## What is not completed

The fixed-radius real quadratic FLUX identity is proved. The general off-corner derivative
is assembled below, but its model instantiation above the degenerate regime still needs the
fourth-moment input of Lipschitz Russo exchange: what remains is that input, not the
fundamental-theorem interface. What follows describes the analytic route and its remaining
model hypotheses. What remains is the radius-sensitive exchange: locally uniform convergence of the
finite-window pivotal series, or a valid Taylor/radius-change remainder estimate followed by the
primitive FTC. A fixed-radius FLUX identity alone does not prove
`HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r`.
`SecondMoment/WindowExchange` additionally proves the finite-window Russo derivative at the actual
cutoff law and reduces the target derivative to two explicit quantitative inputs: a summable `u`
dominating every per-edge pivotal flux uniformly in the radius window, and a nonnegative
`v k → 0` bounding insertion errors. It establishes window-moment convergence without caps and a
Weierstrass domination bridge for the infinite series. It does **not** construct `u` or `v`; the
actual derivative theorem remains conditional on that missing work.

`SecondMoment/Integrated` gives the complementary integrated reduction: monotone radius integrals
of finite-window Russo derivatives converge to the moment increment, provided measurability,
nonnegativity, monotonicity, finite-window interval integrability, pointwise flux convergence,
window-moment convergence, and RHS interval integrability are supplied. The fixed-base FTC and
off-sphere RHS continuity then yield the pointwise derivative. These inputs are not silently
discharged.

`SecondMoment/Integrated/Exchange.lean` replaces the scalar monotone-convergence step by
Lebesgue dominated convergence in the window index.
`SecondMoment/Integrated/RadiusFTC.lean` consequently derives the integrated and pointwise
`p=2` radius identities with `hfluxMono`, `hmomMono` and `hmomNN` removed, and without
requiring the window family to be nested or exhaustive. Instead it retains the meaningful
analytic inputs explicitly: a single radius-integrable majorant for all window fluxes,
`hfluxConv`, moment convergence, RHS continuity, and RHS interval integrability.
The edge-sum form `hasDerivAt_cutMomentReal_two_of_envelope` is the downstream interface
for the envelope construction and its uniform-in-radius specialization. `partialLimitFlux_le_rhsScalarTwo` bounds a finite
partial sum of the *untruncated* pivotal flux; it is not a domination theorem for `windowFlux`.
The `sSup` analytic variant still requires integrability of the pointwise supremum in the
window index, and the constant-bound variant requires an explicit finite-window constant
uniform in that index. The fixed-radius `hfluxConv` is constructed below in `FluxConv/Envelope/Summable.lean`;
the majorant and local interval-integrability are then constructed in `WindowMajorant` and
`Integrated/LocalFTC` before the final source-witness assembly.
`sub_le_sub_false` records only the arithmetic obstruction to deriving flip-difference
monotonicity from observable domination; it is not a source-model nonmonotonicity result.

`SecondMoment/Integrated/FluxBounds.lean` bounds each finite-window cluster by its finite vertex set
and its quadratic flip by twice the square of that cardinality. Combined with the exponential bound
on `cutEdgeDeriv` and local interval integrability of $K'$, this discharges `hfluxInt` on off-corner
windows and, more generally, on compact positive-radius intervals. It also proves almost-everywhere
strong measurability of the window flux. The other flux and moment inputs are still separate.

`SecondMoment/Integrated/WindowFlux.lean` proves `measurable_windowFlux` and `windowFlux_nonneg`
by restricting to the finite Bernoulli product on each window cluster, thereby obtaining a finite
vertex measure and removing pathological infinite-volume `toReal` effects. These are all discharged
for every finite window. The required flux monotonicity and convergence inputs remain distinct.

`SecondMoment/Integrated/Moment.lean` proves nonnegativity and convergence of the moment increments.
`Assembly.lean` removes the unused `hmomMono` hypothesis from the interval and pointwise reductions,
then derives `hmomNN` and `hmomConv` from a finite second cutoff moment. It also proves
`intervalIntegrable_rhsScalarTwo_of_coeffBound` from a finite fourth cutoff moment and a local bound
on `coeffRHS`. Thus `hfluxInt`, `hmomNN`, `hmomConv` and `hrhsInt` have genuine finite-window/local
reductions, while flux convergence and the coefficient bound/continuity are not assumed to follow
from `K_diff` alone.

`SecondMoment/FluxConv` proves that the truncated full-edge pivotal sum converges to `rhsScalarTwo`,
and identifies its difference from the window flux by the exact `insertionDeficit`. The finite-window
closed ghost is verified from the exact merge identity. `tendsto_windowFlux_of_insertionError`
produces `hfluxConv` only once insertion tolerance is supplied; the window weights are not assumed
to enlarge monotonically with the window.

`SecondMoment/Integrated/Completion.lean` is the capstone conditional theorem: it removes the
moment and interval inputs as far as they have been discharged. Its flux convergence, coefficient
continuity, and coefficient bound remain explicit hypotheses.

`SecondMoment/SourceWitness` specializes these inputs to the paper's power-law kernel. It proves
`coeffRHS r = β_c r^{-d-α-1}`, continuity of the coefficient and its bound by
`|β_c|a^{-d-α-1}` on $[a,\infty)$, off-sphere continuity, and interval integrability of
`rhsScalarTwo`. It also gives `isOffCornerWindow_sourceModelWitness` on $[1/2,1]$ and
`sourceModelWitness_sphere_ne` below radius $2$. The resulting instantiated derivative theorem
therefore leaves only flux monotonicity, flux convergence, and the explicit moment hypotheses;
the coefficient-side obligations are discharged rather than assumed.

The canonical `boxEdges` family is included, and every cutoff moment is evaluated exactly to be $1$
below radius $2$ at the source power-law witness. This discharges the small-radius moment inputs,
but the older theorem in `SourceWitness/Main.lean` still presents them as inputs to its conditional
flux assembly.

`SecondMoment/SourceWitness/SmallRadius.lean` closes that degenerate regime directly, without
using that assembly or either flux hypothesis. For `r_0<2`, the source ball consists of the origin
alone, so both excluded sums and `p2RHS` vanish, and `cutMomentReal 2` is locally the constant $1$.
The resulting `hasDerivAt_cutMomentReal_two_sourceModelWitness_of_lt_two` proves exactly
$$\mathrm{HasDerivAt}\;(r\mapsto M.\mathrm{cutMomentReal}\;2\;r)\;
  (\beta_c r_0^{-d-\alpha-1}(M.\mathrm{p2RHS}(r_0)).\mathrm{toReal})\;r_0,$$
with no monotonicity, convergence, exhaustion or finiteness premises. Restricting to $0<r_0<2$
gives the literal small-radius off-corner instance. This is not a proof at $r_0\ge2$: the general
nondegenerate exchange problem, including the envelope work below, remains open.
`SecondMoment/FluxConv/Pointwise.lean` additionally proves eventual agreement of the windowed and
untruncated square flip differences on every finite cluster, including almost-sure convergence of
the relevant connections. The mean-valued insertion still needs a domination argument; no claimed
convergence follows from eventual pointwise equality alone. `FluxConv/Insertion.lean` gives the
corresponding dominated-convergence and weighted-subseries steps: a common integrable envelope
for all windowed and untruncated flip differences, with a summable coefficient-weighted mean,
produces `hfluxConv`.

`FluxConv/Envelope/Defs.lean` defines an unexcluded marked quadratic weight and a full
configuration envelope, with the cubic merge majorant retained on the complement of the
radius-derivative support. `Main.lean` dominates both the windowed and untruncated real flip
differences by that envelope, using cluster-subset inequalities rather than monotonicity of
the ghost. `Compare.lean` identifies the connected-triple deficit against `p2Weight`;
`Correction.lean` sums it as $3|K_0|^4$, and `Reindex.lean` supplies the exact edge/pair
count. Finally `Summable.lean` proves
$$\sum'_e \int^-_\omega \mathrm{unexclEdgeWeight}_e(\omega\setminus\{e\})
  \le M.\mathrm{p2RHS}(r)+3M.\mathrm{cutMoment}(4,r).$$
It uses this finiteness, the landed coefficient comparison and the conversion to real means
to discharge `integrable_envelope` and
`summable_two_deriv_mul_integral_envelope`.  The terminal
`tendsto_windowFlux_of_cutMoment_four` therefore proves
`Tendsto (windowFlux (S n) r) (rhsScalarTwo r)` for every monotone exhaustive finite-window
family, from only `0 < r` and `M.cutMoment 4 r ≠ ⊤`; the first cutoff moment and finite
`p2RHS` prerequisites are derived internally. `hfluxConv_of_cutMoment_four` retains the
pointwise fourth-moment input at every positive radius separately.

This is a genuine fixed-radius `hfluxConv`, not an unproved envelope schema.  It does not,
by itself, spawn a uniform-in-radius majorant for the monotone-free radius FTC or prove
`HasDerivAt`; it also does not establish fourth-moment finiteness above radius $2$ for the
literal critical source witness.

## Uniform-in-radius majorant and the nondegenerate off-corner derivative

`WindowMajorant/Main.lean` proves a genuine finite-window flux domination uniformly in the
window index, not monotonicity of any ghost:
$$
  M.\mathrm{windowFlux}(S n,t)\le M.\mathrm{rhsScalarTwo}(t)
    +3C(M.\mathrm{cutMoment}\,4\,b).\mathrm{toReal},
$$
for every finite-window family $S$ and every $t\in(a,b]$, under an explicit coefficient bound
$|M.\mathrm{coeffRHS}(t)|\le C$ and finite fourth cutoff moment on the window. A finite fourth
moment only at $b$ suffices for this bound via cutoff-moment monotonicity. The packaged
`windowMajorant` is twice the right-hand side plus that constant and is interval integrable
whenever `rhsScalarTwo` is measurable and the same coefficient/moment inputs hold. Its sharp
one-times comparison and the packaged factor of two must not be confused.

`Integrated/LocalFTC.lean` weakens the earlier global conditions appropriately: RHS
measurability is only almost-everywhere strong measurability on the radius window, flux
convergence is required only on `(a,b]`, and the fixed-base FTC uses the restricted measurable
set. It derives moment convergence and RHS interval integrability from the fourth moment and
coefficient bound, and RHS continuity at an off-sphere radius from coefficient continuity.

Combining these with `FluxConv/Envelope/Summable.tendsto_windowFlux_of_cutMoment_four` gives
`SourceWitness/OffCorner.hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner`:
for an arbitrary source off-corner window $[a,b]$, an interior off-sphere $r_0$, and
$\forall t\in(a,b],\,M.\mathrm{cutMoment}(4,t)\ne\top$,
$$
\operatorname{HasDerivAt}\bigl(r\mapsto M.\mathrm{cutMomentReal}\,2\,r\bigr)\;
  \bigl(\beta_c r_0^{-d-\alpha-1}(M.\mathrm{p2RHS}\,r_0).\mathrm{toReal}\bigr)\;r_0.
$$
There is no majorant hypothesis, no `hfluxMono`, no global measurability and no finite-box
substitution. The fourth-moment input on $(a,b]$ and `hsphere` are exactly what remain. The
proof also discharges event geometry beyond radius 2 using $2\|\cdot\|_\infty$, so all
non-even radii are off-corner/off-sphere. In particular the theorem at $r_0=37/10$ on
$[7/2,39/10]$ is a nondegenerate conditional instance. Its member-name
`three_and_seven_unconditional` does **not** mean that `h4` has been discharged: its declared
`h4` assumption remains in the statement.

This is the nondegenerate off-corner radius derivative conditional on fourth-moment
finiteness. It is **not** an unconditional proof of Lemma I.4.1. Above radius 2 the literal
witness's fourth moments are not supplied here. The separate `SmallRadius` theorem remains a
direct zero-derivative computation below 2, not a substitute for this nondegenerate result or
for the missing model moment bounds.

The additional `SourceWitness/Sharpness.lean` wrapper
`hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_subcritical` supplies the
fourth-moment input via the established `cutMoment_ne_top_of_subcritical_first` transfer. It
therefore proves the same off-corner derivative from `betaCrit > 0` and the source sharpness
input: finite uncut first cluster moment at every strictly subcritical intensity. It uses no
uniform-in-β critical-moment bound, does not supply that sharpness input, and does not infer
finite susceptibility from vanishing percolation probability.

`SourceWitness/AlmostEverywhere.lean` clarifies the geometric condition. The vertex-radius
family `sphereRadii` equals the attained radii together with the origin, and at positive radius
`OffSphere r` is equivalent to `r ∉ cornerRadii`. It is countable and Lebesgue-null, so any
nondegenerate interval contains an off-sphere radius. Consequently the off-corner derivative
holds almost everywhere on every off-corner window and at some point of every nondegenerate
such window; the fourth-moment hypothesis remains on all `(a,b]`, and its sharpness-conditional
form remains conditional on `betaCrit > 0` and subcritical first-moment finiteness. These are
almost-everywhere/existence statements, not the removal of the pointwise sphere restriction.
The same module shows that the coefficient-weighted `p2RHS` is nonnegative almost everywhere,
using monotonicity of `cutMomentReal` rather than an evaluation of `p2RHS`.

The earlier generic `RussoInf/FluxTruncation` level vocabulary remains auxiliary infrastructure,
not an alternative proof of the off-corner derivative.

Strict-window left limits and off-sphere continuity of the derivative weight are proved; positive
shells retain the genuine one-sided distinction. No attained-radius two-sided formula or general-$p$
derivative is obtained from these identities.

## The excluded quadratic mass and the source's coefficient three

`SecondMoment.ExclusionSwap` proves the second equality in the source's
(I.4.14), rather than merely bounding the two excluded terms. The midpoint
reflection $x\mapsto y-x$ preserves the radial cutoff kernel and the cutoff
product law, swaps the rooted clusters $K_0$ and $K_y$, and preserves the
indicator that $y$ is outside $K_0$. Each finite-window summand therefore has
the same expectation after this substitution, even without moment-finiteness.

The resulting theorems are
`exclMassQuad_eq_exclMassSqLin` and
`p2RHS_eq_three_mul_exclMassQuad`, with an unconditional real-valued form:
$$M.p2RHS(r)=3\,M.exclMassQuad(r).$$
The two excluded terms are thus identified with the single excluded quadratic
window mass $U$ in (I.4.14), with coefficient exactly $3$ and no use of the
first-moment defect. This identity holds for every `SourceModelData` and every
radius.

This does **not** by itself supply the second-moment regular-variation theorem.
The derivative/absolute-continuity handoff must still be instantiated; the
source's second-moment error decomposition and vanishing or logarithmic
integrability remain separate. In particular, the available Cauchy–Schwarz
bound for `quadPairMass` is not promoted to the required mean-field
second-moment estimate.

## Conditional corner-safe regular variation

`Analysis.SecondMomentRV` proves the linear-ODE-to-RV passage with interval
absolute continuity and an a.e. derivative. For measurable $E\to0$,
$f'=3\alpha(1-E)f/r$ gives index $3\alpha$ regular variation; logarithmic
integrability of $E$ gives a positive power-law limit.
`ModelSecondMomentRV` applies the engine to the real `momOf` second moment and
includes the `momOf_packet` wrapper. These results retain $h_P$ and the model's
AC, derivative, measurability and error hypotheses. They neither construct the
model error nor supply regular variation from the bounded two-sided moment
comparison alone.

## Two-cluster covariance and the connected window remainder

`SecondMoment.Covariance` proves a general extended-cardinality BK instance:
for natural powers $a,b$,
$$\mathbb E[|K_x|^a|K_y|^b \mathbf1(x\nleftrightarrow y)]
  \le \mathbb E|K_x|^a\cdot\mathbb E|K_y|^b.$$
This is the established general `ℝ≥0∞` two-cluster theorem specialized to
`cardFun` powers; infinite clusters are not converted to zero. At the actual
radial cutoff law, translation-invariance of all cluster moments and finite
Tonelli give
$$M.exclMassQuad(r)\le |B_r|\,M_1(r)M_2(r).$$
The bound is unconditional on moment finiteness.

`SecondMoment.CovarianceWindows` also proves this for an arbitrary finite
window, its strict and shell variants, and the reflected linear excluded
mass. It provides real forms under finite first and second moments. The lower
Harris–FKG side is kept separate:
$$|B_r|\,M_1M_2\le M.exclMassQuad+M.connCubeMass.$$
`connCubeMass` is identified with the actual
$E[|K_0|^3\#(K_0\cap B_r)]$. Therefore the full joint window mass obeys a
sandwich with that connected term, not the incorrect whole-`quadPairMass`
product bound claimed by the rejected shortcut.

This is the covariance input of (I.4.16). Vanishing and logarithmic
integrability of the normalized error still depend on the case-specific
connected-moment bounds; no regular-variation conclusion follows from these
inequalities alone.

## Why absolute continuity is indispensable

`SecondMomentObstruction` supplies the explicit witness
$f(r)=r^a2^{\lfloor r\rfloor}$. It is measurable, positive on the positive
ray, monotone there, and satisfies $f'=af/r$ away from the integers.
Nevertheless its doubling ratio is unbounded along the integers, so it is not
regularly varying of index $a$ and cannot have a finite power-normalized
limit. The integers form a null set, so even positivity, monotonicity and a
zero-error a.e. ODE do not suffice.

Thus deleting the interval absolute-continuity premise from the linear
ODE-to-RV theorem is not a legitimate relaxation. The witness is discontinuous
at the integers; it does not address continuous singular examples, and it says
nothing about the actual cutoff second moment beyond keeping `hac` as an
essential model obligation.

## The normalized excluded error and the ODE identity

`Analysis.SecondMomentError` defines the source objects directly:
`p2ExclError` is $E_{2,r}$, `p2Ebar` is $\barar E_{2,r}$, `p2H` is the
normalized first-moment deviation $H_r$, and `p2Flux` is the real second-moment
derivative weight. `Bounds` proves the two parts of (I.4.16) from the accepted
covariance bounds with explicit finite second-moment, connected-moment and
positive-window denominators. `p2ExclError_eq_second_form` verifies the
paper's equivalent numerator using `quadPairMass`.

`Normalized` identifies `p2Flux` with `rhsScalarTwo`, proves the exact
(I.4.14)/(I.4.15) identities through the established scalar normalization, and
discharges $H_r	o0$ from $h_P$ and $E_{0,r}	o0$ from `PivotFlux.tendsto_cutE0`.
The reduced RV theorem still requires second-moment AC, the a.e. radial
identity, measurability of `rhsScalarTwo`, finite tail moments and the vanishing
of the normalized connected-mass ratio. Logarithmic integrability for the
power-law refinement is also explicit, not inferred from pointwise decay.

## Conditional Case-3 assembly

`Analysis.SecondMomentCase3` introduces `case3Driver c r` as the genuine
$(\nabla_{r^c}+r^{-c})$ driver and `connCubeVertexMass` for the per-window-vertex
third moment. `connCubeMass_eq_sum_vertex` decomposes the actual numerator over
the finite window without any `toReal ⊤ = 0` step. The eventual-ratio theorem
proves $C/(|B_r|M_1M_2)\le (K/c_3)(\nabla_{r^c}+r^{-c})$ from
$C\le K|B_r|drv\,M_1^4$ and $c_3M_1^3\le M_2$ — precisely the cancellation that
requires the lower second-moment comparison, not a bounded comparison alone.
The latter is derived separately from the uncut critical volume-tail envelope.

The numerator theorem keeps both the per-vertex `p = 3, q = 0` gap `hgap` and
the distinct $\ell=3$ input `hT3` explicit. The $\ell=4$ polygon majorant is
instantiated from the proved all-radius theorem. The printed $\ell=3$ display
is not silently substituted by the naive column-sum bound, whose remaining
$\chi^3/|B_r|$ term is not general Case-3 decay. These are source hypotheses,
not facts claimed from hTri alone.

Under the additional radial regularity, measurability and volume-tail
hypotheses the file proves $E_{2,r}\to0$ from the driver squeeze, logarithmic
integrability of $E_{2,r}$ and $\bar E_{2,r}$, regular variation of index
$3\alpha$, and a conditional power-law asymptotic for the second moment. The
log-integrability of $\bar E$ uses $\bar E=E_2\Psi-(\Psi-1)$, with
$\Psi=(1+H)(1-E_0)$ bounded on a tail. None of this supplies missing AC, a.e.
derivative, numerator, hT3, measurability or volume-tail data for the canonical
model.

## Conditional Case-1 assembly

`Analysis.SecondMomentCase1` applies the proved mixed fourth-moment inequality
at the actual cutoff law: M4 ≤ 15 M2 M1^4. In particular, finite second moments
give finite fourth and connected third moments. With the existing covariance
denominator this proves the Case-1 error bound
E2 ≤ 15 M1^3 / |B_r|, with M2 cancelled exactly. The first-moment asymptotic
hP gives M1 ≤ 2(α/β_c)r^α eventually, and the lower ball sandwich gives
r^d/|B_r| ≤ 2^d. Thus the explicit rate is
15·8·(α/β_c)³·2^d·r^(3α-d).
When d > 3α, this rate tends to zero and is logarithmically integrable.

The packet also derives logarithmic integrability of E0 from M.exists_error
and the two-sided lattice-ball estimate, not from an additional arbitrary kernel
profile. The normalized Ebar logarithmic integral then uses E2, H and E0 with
their explicit convergence and measurability data. These feed conditional
regular variation, connected-ratio reduction and power-law asymptotics.
Absolute continuity, the a.e. second-moment derivative, rhs-measurability, hP,
finite tail moments, error measurability and logarithmic integrability of p2H
remain source obligations. The mixed fourth-moment proof is reused rather than
replaced by the weaker ordinary M1^7 estimate, and no whole-window product
bound is asserted.

## Measurability from right limits, not absolute continuity

`Analysis.SecondMomentMeasurability` proves the generic dyadic-right-limit
lemma: a function right continuous on a Borel set, with known values off it,
is Borel measurable. Strictly greater dyadic points converge from the right,
so the landed `𝓝[>]` radius statements are used verbatim. The remaining
window jumps need not be removed or equated with closed-window values.

The second-moment derivative weight is the product of the measurable kernel
coefficient and the right-continuous real p2RHS. Explicit nonpositive-radius
calculations reduce the other side to zero, and fourth-moment finiteness at a
larger radius invokes the proved right-limit theorem. The mixed inequality in
Case 1 makes that fourth-moment input follow from a finite second moment;
tail second-moment finiteness promotes globally by monotonicity. Consequently
`measurable_rhsScalarTwo_of_tail` needs no coeffRHS-continuity, hac, hae,
monotonicity of the weight, or two-sided limit at an attained radius.

The real excluded mass is likewise a right-limit combination of quadPairMass
and connCubeMass, with careful finite toReal conversions. The algebraic error
definitions then give global measurability of p2ExclError and p2Ebar. These
facts discharge hmR and the error-measurability premises in the new case
consumers without adding hypotheses. They do not establish absolute continuity
or the a.e. radial derivative itself; those remain separate inputs.
