# Proposition I.4.20: proof status

The general scalar second-induction assembly is proved separately under its
stated decorrelation inputs. It is **not** an unconditional proof of the higher
moments of the canonical cutoff model.

## Case 1 (`d > 3α`)

`VolumeMoments/HigherMoments/I420Case1` proves the Case 1 decorrelation at the
actual independent-edge law `edgeMeasure π`, for countable vertex type `V`.
It uses the loop-independent cardinalities and real-valued expectations, not a
finite-vertex test graph.

- `mixedExcl π o a b B` is
  `E[|K_o|^a ∑_{y∈B} 1(y∉K_o) |K_y|^b]`;
  `prodFactor π o a b B = ∑_{y∈B} E|K_o|^a E|K_y|^b`;
  `windowMoment π o k B = E[|K_o|^k |K_o ∩ B|]`.
- `mixedExcl_le_prodFactor` comes from BK, and
  `prodFactor_le_mixedExcl_add_window` comes from Harris–FKG plus equality of
  the two clusters on a connection event. Neither discrepancy inequality is
  hypothesized.
- `discrepancy_toReal` uses finite product/window moments, so the real-valued
  subtraction does not exploit `ENNReal.toReal ⊤ = 0`.
- `case1_decorrelation` proves the required ratio with `a=ℓ+1`, `b=p−ℓ`,
  ℓ≤p, from explicit homogeneity, higher-moment finiteness, upper tree-graph
  order `(2p+3)α`, and lower product order `d+2pα`.
- `wMom_order_of_treegraph` and `prodFactor_order_of_asymptotics` separate the
  exponent bookkeeping. In particular the first's
  `E|K|^(p+2)` tree-graph assumption and the sources' regular-variation order
  assumptions are retained, not manufactured.

The equality case at zero opening probabilities checks the exact exclusion and
window normalizations. It is not a lattice sharpness computation.

## Endpoint mass transport

`HigherMoments/I420Endpoint` supplies the equality of the two endpoint mixed
moments without invoking scalar symmetry or requiring any window symmetry.
For each `y`, `z ↦ x + y − z` transports `x` to `y` and `y` to `x` while
preserving the disconnection complement (up to `connects_symm`). The per-site
and finite-window theorem proves

```text
E[|K_x|^a 1{y ∉ K_x} |K_y|^b]
  = E[|K_x|^b 1{y ∉ K_x} |K_y|^a].
```

`mixedExcl_swap_window` states this for arbitrary `a,b` and arbitrary finite
`B`, and `mixedExcl_toReal_swap_window` supplies its real-valued version, which
matches the endpoint `hmass` condition of the analytic second induction.
`radial_reflect_norm` and `cutKernel_reflect_norm` prove that the normalized
radial lattice cutoff kernel is preserved by these midpoint reflections, so
`mixedExcl_cutKernel_swap` instantiates the result at the actual source model.
The proof uses only profile-preserving permutations, not root-independence of
the mixed joint moment, finiteness assumptions, or a finite-box replacement.

## Case 2 (`d = 3α`, hydrodynamic condition)

`VolumeMoments/HigherMoments/I420Case2` proves the cutoff-model
Cauchy–Schwarz comparison. `jointMoment_le_cs` uses ENNReal Hölder and
preserves infinite moments. `jointMoment_le_of_bounds` inserts (I.4.19) at
order `2p+2` and universal tightness `E[|K∩B|²] ≤ M_r E|K|`. The resulting
factor is `√(C (M₂/M₁)^(2p+1) M₁) √(M_r M₁)`.

`case2_decorrelation_error` and `jointUpper_isLittleO` compare that factor to
`|B_r| (M₂/M₁)^(p−1) M₁²` at `d = 3α`. The account uses both sides of
`E|K| ≍ r^α`, `M₂/M₁ ≤ γ (E|K|)²`, `M_r = o(r^((d+α)/2))`, and the actual
Lemma I.4.6 ball-volume asymptotic. They remain explicit inputs except the
last two, whose definition of `Hydro` and `M.ball_count` are instantiated.

The earlier BK/FKG Case 1 discrepancy supplies the identification of the
mixed-window moment with the excluded-moment discrepancy needed in the final
application, but doesn't supply (I.4.19) at order `2p+2`, universal-tightness,
or moment–asymptotic inputs. This is therefore the Case 2 error estimate, not
an unconditional second-induction or sharpness result.

## Case 3 (triangle condition), conditional decorrelation chain

`HigherMoments/I420Case3` builds the normalized decorrelation interface from
canonical pair factors and excluded moments. `HasTreeExpansion` and
`HasPolygonBound` retain explicit general I.4.17 and I.4.18 inputs. The proof
sums over ball vertices then path lengths, turns the resulting polygon bound
into a real averaged discrepancy, and makes it little-o of the induction target
when the uniform polygon factor tends to zero. This is a conditional chain, not
completion of Case 3, I.4.20, or the source's triangle-bound verification.

### Tree expansion from I.4.17

`I420Case3/TreeInterface` proves the moment identities between `clusterVol` and
`Percolation.cardFun`, and hence between `pairFactor`/`I417A.momentProd` and
`pairExcl`/`I417A.rawDiff`. `AuditM1.hasTreeExpansion_of_i417` constructs
`HasTreeExpansion` for arbitrary finite windows and exponents $a,b\ge1$, with
$p=a+b-1$, the connection-kernel powers from `I417Base.iterPow`, and the integer
`I417SummedClose.composedCoeff` coefficients. Its hypotheses are strict edge
probabilities and constancy of the first-moment row sums. It does not assume
finiteness of higher moments, subcriticality, or homogeneity of later moments.

`AuditM1.hasTreeExpansion_family` puts this on the induction-index surface. It
covers exactly `ℓ + 1 ≤ p`, where the second exponent `p - ℓ` is positive. It
does **not** cover `ℓ = p` (`b = 0`), while the existing
`case3_hAend_hAmid` wrappers quantify their tree input over all `ℓ ≤ p`.
No zero-exponent extension is asserted: `pairExcl` contains a non-connection
indicator and is not generally equal to `pairFactor`. The original broad-range
wrappers retain that input; `SplitPolygon` below supplies a corrected wrapper
whose tree range is exactly `ℓ + 1 ≤ p`.
For the cutoff model, `CutPoly.Bridge` now answers the semantic bridge question.
`AuditM2.iterPow_eq_Kpow` proves the two iterates equal for every `ℝ≥0∞` kernel,
`cutPoly_eq_iterPow_cutProb` identifies their canonical cutoff specializations
under finite cutoff susceptibility, and `hasTreeExpansion_cutPoly` transports
the positive-exponent tree record to `cutPoly` itself.

### Genuine cutoff polygon powers and the threefold corner

`I420Case3/CutPoly` defines `cutPoly` from the real cutoff matrix powers
`I418C.polyK`, identifies it with the extended-real `Kpow` under finite cutoff
susceptibility, and proves `powMomentAt_cutProb_one`. Under the explicit
first-moment asymptotic `hP` and finite-triangle hypothesis `hTri`,
`CutPoly.cutPoly_le_rate` gives the source polygon estimate for $j\ge4$.
`exists_hasPolygonBound_cutPoly` combines it with the proved pointwise $j=3$
bound to give a genuine `HasPolygonBound` with factor
`max M.triSelf (C * ((M.nablaTail (r^c)).toReal + r^(-c)))`.

This factor is deliberately not described as vanishing.
`one_le_polyK_three_of_chi_ne_top` proves that the diagonal threefold power is
at least one. Consequently `one_le_Bpoly_of_hasPolygonBound`, and the eventual
forms `no_vanishing_uniform_polygon_factor` and
`not_exists_vanishing_hasPolygonBound`, show that no uniform polygon factor can
tend to zero when the window contains the origin and the cutoff first moment is
finite. Under triangle-tail decay, `tendsto_polygonFactor` instead has limit
`M.triSelf`. Thus the old single-factor `Bpoly → 0` interface cannot consume
these genuine cutoff powers at its $j=3$ corner.

`prodFactor_le_mixedExcl_add_cutPoly` is only the resulting pointwise
discrepancy bound: it does not prove the normalized little-o limit,
triangle-tail convergence, or the averaged threefold replacement. None of
those is claimed here.

### Split polygon interface and the corrected tree range

`I420Case3/SplitPolygon` adds the replacement interface rather than weakening
`HasPolygonBound`. `HasSplitPolygonBound` bounds
$\sum_{y\in B}\mathrm{poly}\;y\;3$ by $|B|\,B_{\mathrm{three}}$, and separately
bounds the pointwise entries for $4\le j\le p+2$ using $B_{\mathrm{tail}}$.
This is the averaged $j=3$ shape used by the normalized discrepancy; it never
requires the diagonal threefold power itself to tend to zero. For $p\ge1$,
`HasPolygonBound.hasSplitPolygonBound` gives the conservative conversion with
the same factor in both slots.

`polygon_sum_le_split`, `prodFactor_le_mixedExcl_add_splitPolygon`, and
`discR_le_splitPolygon` carry the two factors through the canonical ENNReal and
finite-real calculations. `case3_i421_family_split` proves the normalized error
limit when both factors tend to zero.
`case3_hAend_hAmid_split` proves the endpoint and middle-index ratio limits
from that split input, moment log-convexity, and tree records only for
`ℓ + 1 ≤ p`; it has no unused `ℓ = p` tree premise and no separate denominator
comparison premise. `case3_hAend_hAmid_split_of_i417` goes further and
constructs all those tree records from `AuditM1.hasTreeExpansion_family`, using
strict edge probabilities and first-moment row constancy.

`SplitPolygon/Model` also instantiates the genuine `cutPoly` near/far estimate.
For a nonempty finite window `B` and near set `s`, with the complement in `B`
beyond norm `R`, `sum_polyK_three_le_near_far` proves
$$\sum_{y\in B}T^3_{\beta_c,r}(0,y)\le |B|\nabla_R+|s|\nabla_{\beta_c}.$$
`cutPoly_three_sum_le_near_far` puts this in ENNReal averaged form, and
`exists_hasSplitPolygonBound_cutPoly_near_far` combines it with the genuine
higher-depth cutoff rate. Here the threefold factor is
$\nabla_R+(|s|/|B|)\nabla_{\beta_c}$. `tendsto_near_far_factor` proves that
this factor tends to zero if the triangle tail and the cardinality ratio both
do so. `SplitPolygon.NearWindow` now supplies those choices for the actual
source model. For fixed $0<\theta<1$, `exists_source_near_far_ratio` returns
the finite source balls, near sets at scale $r^\theta$, the required far-region
nonempty source windows for each nonnegative radius, the far-region condition
for every $r\ge1$, and a proof that $|s_r|/|B_r|\to0$ using the normalized
ball-count asymptotic.
`SplitPolygon.Tails` proves `tendsto_nablaTail_rpow` and
`power_nablaTail_limits`, so one base hypothesis $\nabla_r\to0$ gives every
positive power-rescaled tail limit. Finiteness of the triangle alone is not used
to prove this decay.

`CutPoly.Bridge` closes the common-polynomial obligation. In particular,
`iterPow_eq_Kpow` is unconditional in the `ℝ≥0∞` setting, and the full cutoff
specialization uses exactly the finite first-moment hypothesis already needed
to identify `cutPoly` with `Kpow`; depths zero and one are checked separately
without that finiteness input. `SplitPolygon.Eventually` gives the split error
assembly with finite-window and moment inputs at time infinity only.
`case3_i421_cutPoly_near_far` now combines all of these results and proves the
normalized I.4.21 error limit for the canonical cutoff family. Its explicit
inputs are the first-moment asymptotic, finite triangle, decay of the chosen
near/far tail and near/window cardinality ratio, decay of the power-rescaled
triangle tails, moment finiteness and non-degeneracy, and the usual
second-moment lower comparison. Its specialization
`exists_case3_i421_cutPoly_source` chooses the source balls and $r^\theta$
near sets directly and takes only the base tail limit in addition to the
first-moment, finite-triangle, moment-finiteness and lower-comparison inputs.
Thus the tail/cardinality construction is no longer an unimplemented analytic
promise; deriving its base tail and model-moment premises remains the
model-specific work.

`SplitPolygon.DirectEventually` extends the same correction to the direct
endpoint/middle-index assembly. Its `case3_hAmid_of_i421_eventually` and
`case3_hAend_hAmid_split_eventually` accept finite-window and moment inputs
only at time infinity. `case3_hAend_hAmid_cutPoly_source` instantiates these
on the actual source windows and proves both direct ratio limits. The direct
source theorem derives its denominator comparison using constant one.
`SplitPolygon.MomentHom` additionally proves `powMomentAt_cutProb_perm` and
`powMomentAt_cutProb_apply_eq_zero`: every cluster moment is invariant under a
profile-preserving permutation, including all cutoff translations. Consequently
`case3_hAend_hAmid_cutPoly_source_of_finite` discharges both window homogeneity
and window finiteness. Only the root moment-finiteness range, base tail limit and
source two-moment inputs remain separate. The wrapper
`isLogErrorFunction_nablaTail_of_HD_case2_or_case3` supplies that tail limit from
the HD(2)-or-HD(3) disjunction through its second projection; it is not inferred
from triangle finiteness alone.

The interface repair, polynomial bridge and conditional canonical-cutoff error
assembly are therefore complete. Their tail/cardinality and moment hypotheses
remain genuine analytic obligations rather than conclusions about the source
model. No constant is set to zero artificially, and no convergence is inferred
from the nonvanishing uniform cutoff factor.

### Denominator comparison by log-convexity

`I420Case3/MomentLogConvex/Defs` proves the one-step Hölder inequality
`(E|K|^(j+1))^2 ≤ E|K|^j E|K|^(j+2)` in `ℝ≥0∞`, with finite-real conversions
under explicit moment-finiteness hypotheses. Its iterated Lyapunov consequence
`MomentLogConvex.biasTarget_le_mul_momR` proves
`biasTarget m₁ m₂ p ≤ m_a m_b` for $a,b\ge1$ and $a+b=p+1$.
`biasTarget_le_mul_momOf` transports this to a radius-indexed family of laws.

`case3_hAend_hAmid_of_hIH'` removes the separate zero-index comparison premise
from the induction-hypothesis wrapper, and `case3_hAend_hAmid'` removes the
explicit denominator comparison entirely, using constant one. These wrappers
still retain their original vanishing-uniform-polygon, tree, finite-moment,
homogeneity, edge, window, and lower-comparison hypotheses. Log-convexity does
not repair the threefold polygon obstruction or discharge any model asymptotic.

### Lower second moment from the critical volume tail

`SplitPolygon.TailLower` proves `momOf_cutProb_eq_toReal_cutMoment`, matching
every canonical cutoff real moment with the source `cutMoment`. Its
`case3_hgm_of_tail` theorem combines the already-proved layer-cake optimization
in `Analysis.Route3` with cutoff-to-uncut stochastic domination: from an uncut
critical volume-tail bound $C/\sqrt n$ and finiteness of the cutoff second moment,
the actual `hgm` inequality holds with $c_3=(4C+1)^{-3}$. This proves the lower
comparison rather than assuming it. The uncut volume-tail bound and second-moment
finiteness remain explicit model inputs; they are not inferred from the first
moment, the upper moment inequalities, or the finite triangle alone.

`exists_case3_i421_cutPoly_source_of_tail` applies this comparison to the actual
source-ball normalized cutoff error theorem. The uncut volume tail and
second-moment finiteness are inputs, but no independent `hgm` premise is needed.
The remaining inputs are the first-moment asymptotic, finite triangle, base
triangle-tail decay, and the explicitly stated root-moment range. Theorems
`hTail` (the open-triangle-tail decay) and `hVolTail` (the uncut volume-tail
bound) remain deliberately separate hypotheses.

### Scaled-ℓ∞ low-order cutoff moments

`SplitPolygon.LowMoments` proves `powMomentAt_ne_top_of_le_four` when the
normalized norm is a positive multiple of `FiniteVolume.linfNorm`: the actual
first, second, third and fourth cutoff moments are finite from a finite first
cutoff moment. This uses native third- and fourth-moment proofs, not a limit or
a high-temperature substitution.
`exists_case3_i421_cutPoly_source_of_tail_three` then proves the normalized
Case-3 error at `p=3` with the required root-moment range supplied by that
single finite first moment and the other independent source inputs. It does not
supply order $5$, arbitrary order, or general-$p$ Case 3.

### HD(3)-scoped source instantiation

`I420Case3.Scope` supplies the first-moment/HD-tail instantiations without asserting
new probabilistic inputs. `case3_hAend_hAmid_cutPoly_source_of_HD_case3` gives
the direct source-ball conclusion with `hP` instantiated by
`I42C.first_moment_asymptotic_of_rpow_lower` and `hTail` by the second projection
of `isLogErrorFunction_nablaTail_of_HD_case2_or_case3` at the third HD disjunct.
`case3_i421_cutPoly_source_of_HD_case3` gives the corresponding normalized
error version with window finiteness transported to the root by translation.

`case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux` additionally identifies the
multiplicative ODE error with
$1-(1-{\cal E}_0)(1-{\cal E}_1)$ using `PivotFlux.cutMass_ODE_of_flux`. It derives
finiteness, positivity and the uniform error bound from its other premises, but
retains the derivative/flux handoff, second-moment finiteness, the lower
two-point bound and cut-error measurability. `tendsto_cutError_of_tendsto_cutE1`
reduces the vanishing error to the shipped standardization limit plus $E_1\to0$.
`openTriangleSelf_lt_top_of_source_sqrt` is only a conditional $\ell^2$
factorization wrapper: it does not derive finite triangle mass from HD(3).

The HD(3) hypothesis, derivative/flux handoff, second-moment and lower two-point
`Scope.Measurability` proves `measurable_cutE0` and composes the defect as
`measurable_cutError_of_measurables`. The remaining exact input is now isolated:
`measurable_cutError_of_stats` takes only `hmass`, `hpair`, and `hconn` for the
three real cutoff statistics. `cutE0` itself is not a remaining measurability
obligation. `pairMass` and `connMass` still have no general radius-regularity
proof, and `hmass` stays explicit where `ENNReal.toReal ⊤ = 0` would obstruct
monotonicity.

The HD(3) hypothesis, derivative/flux handoff, second-moment and lower two-point
bounds, cut-error measurability of the two cluster-dependent statistics,
higher-moment finiteness, second-moment lower comparison and finite triangle
condition all remain separate model inputs. The
first-moment and tail-scope wiring is proved; the underlying ODE and moment
propositions are not thereby completed.

## What is not closed

- Case 3 remains incomplete: the corrected tree range, polynomial bridge,
  finite-window near/far estimate, source-ball cardinality construction and
  conditional canonical-cutoff error assemblies are proved. The base
  triangle-tail limit, first-moment asymptotic and model moment/second-moment
  inputs still need to be derived. The direct endpoint/middle-index asymptotics
  now have translation homogeneity and window finiteness discharged, but retain
  their root finite-moment requirements.
- The ordinary general-index tree-graph bound must still be transported to
  the canonical law at the desired order, and first/second moment asymptotics
  must be derived from the source model. The first-moment and ODE obligations
  are separate from the completed I.4.17 diagram bound and the log-convexity
  comparison.
- The second induction remains a correctly conditional consequence of the
  paper's decorrelation estimates, not a substitute for their three probabilistic cases.

Independent strict builds and axiom audits show only standard axioms for the
Case 1 results.
