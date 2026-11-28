# Spatial limits, explicit tails and correlation reductions

This note records the independently reviewed packets accepted from `smwzt36y2`.
Their supporting Lean results are conditional only in the hypotheses explicitly
listed below. Nothing here completes the paper or its named canonical-model inputs.

## Spatial-moment convergence

`Analysis/GyrationMoments/Limit` proves the monotone extended-nonnegative
sup/`tsum` interchange. It obtains

```text
gyrationMomentUncut M = ⨆_r gyrationMoment M r
```

and the analogous identity for every even displacement moment. The cutoff
moments converge to the uncut value, with real-valued limits under finiteness of
that value. The equivalence between a radius-uniform finite cutoff bound and
finiteness of the uncut numerator is proved, not merely the previous one-sided
bound. The canonical uncut numerator is not thereby proved finite, and the
gyration ODE, two-point asymptotics and superprocess limits remain open.

## The I.1.7 constant and its actual remaining inputs

`Analysis/ClusterVolumeTail/I17` gives an explicit version of Proposition I.3.2
at `a = 2`. The chi-squared constant is evaluated as

```text
A3 = √2 A1 / √A2,    A4 = √2 A1 / (√A2 √π).
```

For first- and second-moment asymptotics with the I.1.6 normalization, the
resulting tail constant is `α/β_c √[2/(πA)]`. The generalized inverse of
`f(r) = r^(2α)` is evaluated above the chosen threshold, so the integer-tail
factor is genuinely $n^{-1/2}$, not an informal identification of an `sInf`.

The model theorem `model_tail_from_cutMoment` preserves all genuine inputs:
weak convergence of normalized size-biased laws to $\chi^2$, the I.3.5
restoration estimate, almost-surely finite critical clusters, finite first and
second cutoff moments, positive volume-law means and size-biased means, a
probability-measure interface for the size-biased laws, and `β_c > 0`.
The file does **not** derive weak convergence from moment determinacy, prove
restoration, establish the moment asymptotics, or provide the varying
critical-dimensional $A_r$ inverse. Hence it supports the route to I.1.7 but is
neither Theorem I.1.6 nor Theorem I.1.15, and is not a superprocess theorem.

## The pinned star and the covariance residual

`Correlation/I417/General/QZeroRepairAudit/PinnedStar` defines the repaired
`q = 0`, `p = 3` star with an explicit diagonal `χ⁵` correction. The two
directions are:

* `hasCovBound_of_hasPinnedStar`: the pinned star plus separate nonnegative
  comparisons `T³ ≤ c₃T` and `T⁴ ≤ c₄T` gives `HasCovBound` with the displayed
  constant conversion. First cutoff moments are required.
* `hasPinnedStar_of_hasCovBound`: the target covariance bound plus first,
  second and third cutoff moments gives the pinned instance with `(1,2,C₅)`.
  This uses the already proved `(2,1)` product gap, not a new star argument.

The first direction is not a proof of `HasCovBound`: the pinned star and its
matrix-power comparisons are substantive geometric inputs. The explicit
correction avoids reintroducing the false two-term diagonal statement.

## Log-free marginal convolution obstruction

`Analysis/LatticeConvolution/LogFreeMarginal` considers the explicit profiles
$a = 2$ and $b = d-2$, at normalized lattice dimension at least two. On the
half-radius window, both factors are comparable to $\|x\|^{-d}`. The normalized
ball-count asymptotic produces a positive lower bound at arbitrarily large
window radii, also for the full extended-nonnegative lattice convolution.
Consequently no global power-decay majorant of the asserted form exists for
this explicit marginal pair, in particular at `d = 6`.

This is an obstruction to removing the logarithm from that profile/convolution
route. It is not a counterexample to the marginal convolution theorem, whose
side condition supplies logarithmic decay, nor is it a refutation of HD(2) or
an instantiation of any percolation two-point estimate.

## The second-moment lower tail

`Analysis/SecondMomentCase3/CriticalVolumeTail/SecondMoment/Lower` proves the
Paley–Zygmund truncation inequalities and transfers lower tail bounds to the
uncut critical law by the correct increasing-event domination. Under first-
and second-moment asymptotics it proves an eventual $1/(Cn)$ lower tail, using
$r_n=(4n/\kappa)^{1/\alpha}$ directly, with no need for an inverse moment
function. The asymptotics and finite cutoff moments remain inputs. This is not
a proof of `CriticalVolumeTail` or the $n^{-1/2}$ first-order tail law. The
last two-atom arithmetic comparison is not a complete optimality construction.

## Case-1 logarithmic error and defect measurability

`Analysis/SecondMomentCase1/Source/LogError` proves that `cutE1` is globally
measurable, that eventual negative-power decay makes it a logarithmically
integrable error function, and that Case 1's decay bound gives the normalized
first-moment error `hHlog`. The old separate measurability and eventual
first-moment hypotheses are derived on the relevant tail.

This is a conditional producer of `hHlog`, not a proof that its defect bound or
its first-moment asymptotic holds canonically. The original radial-window
bundle, continuity data, endpoint second cutoff moment and critical-mass
divergence remain hypotheses. No Case-3 triangle or uncut critical-tail premise
was introduced. A proposed extra I.4.13 transformation was excluded as a
duplicate: production already proves both halves of that lemma.

## The Hydro definition

The I.1.14 coverage entry was a stale definition gap, not a missing Lean
object. `SourceModelData.Mr` is the natural-number infimum of the source median
set, and `SourceModelData.Hydro` is the named normalized median limit. The
formal definition is therefore FULL. Its production from HD(3), from
large-distance HD(3), and from HD(2) with $\alpha > 2$ remains conditional as
recorded in `CRITICAL_LRP_HYDRO.md`; Case 1 and the critical estimates are not
supplied by these packets.

## Both median clauses of Corollary I.2.15

`Tightness/I215` proves the cutoff bound
`M2I215.Mr_le_rpow_of_spatialTwoPointAverage` and the uncut bound
`M2I215Uncut.MrCrit_le_rpow_of_spatialTwoPointAverage`. The only remaining
source-level input is `SpatialTwoPointAverage M`, the conclusion of the cited
Theorem I.2.13, available through an explicitly named predicate.

For the uncut median, the packet does more than monotonicity: it proves critical
translation invariance, the exact median identity, normalized-window averaging,
the median-squared bound and the uncut two-point path-sum identity. Thus both
source clauses are present with one uniform constant for all $r \ge 1$.
The corrected $r^{+d}$ median inequality is used, not the inconsistent printed
$r^{-d}$ display. The corollary remains PARTIAL because I.2.13 itself is open.

## Exact single-branch calculations, not a replacement cover

`Correlation/SixPoint/MixedK2/SixthMoment/HubOne` evaluates the single-branch
variant at exactly $(E|K|^2)^2(E|K|)^3$, with pattern independence, and bounds
it by $(E|K|^2)^2(E|K|)^5$ without moment-finiteness premises. The fully
collapsed tuple $c=x$ supplies the expected root connection probability.

The separate `SixCoverOne` predicate is an explicit unverified premise, not a
repaired cover. No global validity is asserted for it. No compiled
single-branch counterexample was submitted. In particular, this does not close
`CaseTwo.SixthMomentMixed`, Case 2, or the full labelled-tree/BK decomposition.

## Further source-step packets

`Analysis/SecondMomentCase3/CriticalVolumeTail/TwoIntensityComparison` derives
the cited critical-tail envelope and Case-3 moment gap from a genuine
`TwoIntensityTailComparison` and `SusceptibilityBound`. It preserves the actual
source normalization and proves the $n\mapsto(\beta_c-n^{-1/2})$ optimization.
The output constant is `max 1 (max (2/β_c) (2K+8AK/β_c))`. The two hypotheses
and their canonical instantiation are not proved. The Case-3 consumer requires
`cutMoment 2 r ≠ ⊤` for all $r \ge 1$, and supplies no other moment asymptotic.
See [the tail comparison note](CRITICAL_LRP_TAIL_COMPARISON.md).
The relative-entropy/decision-tree input remains open.

`Correlation/SixPoint/SevenPoint` proves `exists_sevenShape`: on any countable
simple graph with all seven terminals reachable from the root, it constructs
one of 840 nine-arm edge-disjoint walk systems, including arbitrary collapsed
tuples. The actual event-probability union bound follows. This avoids the hub
collapse without claiming the bipartite-class mass estimate. Naive grouping
would produce $\chi^6$ instead of $\chi^5$, so the actual mixed sixth moment
remains unresolved.

`Correlation/I411/RowSumCore` and `Correlation/I411/RowSum` formalize the
summation step of I.4.11, in finite real and countable extended-real forms.
Their declaration namespace is `PercLib.CriticalLRP.I411`, so all helper
declarations are included by the production-wide axiom audit. Two row bounds
give $\chi^2$ times the open-triangle sum, and the denominator normalization
uses nonempty `B` and `χ > 0`. Equality holds when the row sum is exactly χ.
A one-point Unit model attains it. The two-copy rewriting of the cluster
numerator and the I.4.12 gap still remain necessary. See
[the row-sum note](CRITICAL_LRP_I411_ROW_SUM.md).
