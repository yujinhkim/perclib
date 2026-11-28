# perclib

Mathematical formalisations in Lean 4 using mathlib.

## Plan

The current plan is in [docs/ROADMAP.md](docs/ROADMAP.md), the decisions behind it in [docs/DECISIONS.md](docs/DECISIONS.md), and the working rules in [docs/COORDINATION.md](docs/COORDINATION.md). The other files in `docs/` are background reference.

## Build

Install [Lean using elan](https://lean-lang.org/install/), then run:

```sh
lake exe cache get
lake build --wfail
```

The project pins Lean **4.35.0**, mathlib **4.35.0**, and all dependency revisions.
Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` in sync when deliberately updating dependencies.

## Layout

- `PercLib/`: definitions and proofs.
- `PercLib.lean`: imports every project module that the default build should check.
- `PercLib/Basic.lean`: a small initial theorem, `PercLib.two_mul_le_add_sq`, proving `2 * a * b ≤ a ^ 2 + b ^ 2` for real numbers.

Add each new proof module to `PercLib.lean` so `lake build` checks it.

## Automated verification

[GitHub Actions](https://github.com/tomhutchcroft/lrp/actions) builds pushes and pull requests with warnings treated as errors. It also audits the axioms of declarations in namespace `PercLib`, allowing only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. This rejects `sorry`/`admit` placeholders and additional axioms in completed proofs.

The initial inequality is a build check for the environment, not a research result.

## Critical long-range percolation I

The `PercLib.CriticalLRP` development formalizes parts of Hutchcroft's
*Critical long-range percolation I*. It is not a complete formalization of the
paper. Use the [source coverage ledger](docs/CRITICAL_LRP_COVERAGE.md) for the
item-by-item status and explicit open assumptions. The
[progress dashboard](docs/CRITICAL_LRP_DASHBOARD.md) separately tracks current
validation, research, unresolved model inputs, and the source-only mirror. Recent continuation results
include the normalized lattice-counting proof of Lemma I.4.6 and the
arbitrary-norm rescaling used there, as well as covariance and finite-second-
moment versions of Lemma I.4.7 for the source cutoff law. The linked notes for
[I.4.6](docs/CRITICAL_LRP_CONTINUATION.md), [I.4.7](docs/CRITICAL_LRP_I47.md),
and [logarithmic integrability in I.4.9](docs/CRITICAL_LRP_I49_LOG.md)
distinguish completed results from conditional model-input reductions and
record their local build and axiom checks. Newer additions cover the analytic
reduction in I.4.8, windowed and finite-translation model components for I.4.9,
and the exact gap-event/diagram components of I.4.11; see
[the I.4.8 note](docs/CRITICAL_LRP_I48.md) and
[the I.4.11 note](docs/CRITICAL_LRP_I411.md). At arbitrary normalized norms,
`OffCorner.SourceCutoffAllMoments` proves the all-order ordinary cutoff moment
bound from the first moment, and `Scope.AllMoments` records the resulting
Case-3 and tail-measurability consequences. Sharpness and the remaining ODE,
triangle, and tail inputs are still hypotheses; see
[the Case-3 ledger](docs/CRITICAL_LRP_I420.md), which also records the route
from averaged critical two-point bounds to critical-mean divergence and the
resulting weaker Case-3 interface. `RadiusMeasurability.Statistics` proves
unconditional global defect measurability, while
`OffCorner.AeDerivativeHandoff` supplies the off-corner derivative, interval
absolute continuity, and AE flux/ODE transport with the scalar-regularity and
probabilistic hypotheses left explicit. `Analysis.AEHigherMoments` extends the
a.e. integration and moment-induction interfaces to higher moments, while
retaining the unproved third-moment AC/derivative and second-moment RV inputs.
The
[cubic/triangle continuation note](docs/CRITICAL_LRP_CUBIC_TRIANGLE_CONTINUATION.md)
records ratio-based moment induction, finite triangles and two conditional
tail-convergence routes under explicit Gram profiles. These routes retain the
profile hypothesis rather than deriving it from HD(3).
[Regular variation](docs/CRITICAL_LRP_MOMENT_REGULAR_VARIATION.md)
adds first-moment asymptotic, measurability and driving-data interfaces, while
keeping the second-moment RV input independent of $h_P$ alone.
`Analysis.ModelSecondMomentRV` derives it only from explicit second-moment AC,
an a.e. linear ODE and error asymptotics; that model data is still open.
`SecondMoment.ExclusionSwap` additionally proves the exact identity
`p2RHS = 3 * exclMassQuad` by reflecting the actual radial cutoff law.
`SecondMoment.Covariance` and `CovarianceWindows` now also prove the two-cluster
covariance bounds: the disconnected excluded mass is at most |B_r|M1M2, with
`connCubeMass` retained separately in the lower and joint-window bounds.
These prove the covariance estimate, not the vanishing of its normalized error
or regular variation.
`SecondMomentError` also defines and analyzes the normalized source error,
proves its covariance bounds and exact ODE identities, and reduces the RV
premise to the appropriate connected-mass ratio and radial regularity.
`SecondMomentCase3.ProductGap` proves the Case-3 numerator consumer from
the established `(2,1)` product gap, removing the old `hgap` and restoring
no star. Its regular-variation and asymptotic wrappers retain the actual ODE,
triangle, moment, first-moment and measurability/log-integrability inputs;
see [the product-gap note](docs/CRITICAL_LRP_PRODUCT_GAP.md).
`RadialRegularity` subsequently derives the window family and the
first-moment/radial hypotheses (`hP`, `hlogH`, `hlogE0`, AC/AE and error
measurability), retaining the second-moment tail, uncut critical mean, moment
gap, triangle/tail and continuity inputs. See
[the radial-regularity note](docs/CRITICAL_LRP_RADIAL_REGULARITY.md).
`TriangleFromHD` subsequently derives the finite triangle and logarithmic tail
from the literal HD(3) premise, while `TailRoute` uses only `IsLogErrorFunction
∇_r` instead of a pointwise bound. `FiniteMoments`, `AmbientParameters` and
`MomentGapAudit` discharge or clarify further wrapper inputs, and
`CriticalVolumeTail` isolates the still-unproved uncut critical tail beneath the
moment gap. HD(3), that tail and the other genuine model inputs remain premises.
`QZeroRepairAudit.ProductGap` now proves the product half of the additive repair,
but does not prove its covariance input. See [the Case-3 reduction note](docs/CRITICAL_LRP_CASE3_REDUCTIONS.md)
for exact scopes. `SecondMomentCase1.Source` proves both Case-1 clauses of
I.4.15 from Proposition I.4.2's first-moment limit and (for the sharp clause)
its logarithmic error, with no separate radial or Case-3 hypotheses. See
[the Case-1 source note](docs/CRITICAL_LRP_CASE1_SOURCE.md). The older
conditional Case-3 numerator/ratio assembly and second-moment asymptotic remain
available for the optional q-zero star route.
`Correlation.I417.General.QZeroStar` identifies that per-vertex numerator
with the connected one-copy star moment and its labelled `(p+1)`-point
expansion. It proves the exact q=0 moment-gap split and shows that the
existing marked family vanishes at q=0; it does not supply the remaining
ell=3/ell=4 tree-count bound. See
[the q=0 note](docs/CRITICAL_LRP_I417_QZERO.md).
The old Case-3 `hcase3` is now proved uninhabited: its pointwise `ℓ = 3`
bound is incompatible with the vanishing driver. `SummedThree` and
`ConsumerGap` replace it by derived near/far window bounds, with the actual
`hgap` still open; `MarkedPolygon` and `EllThreeObstruction` record the
separate alternative residuals and Case-1-only column route. The complete
`WindowedEllThree` bundle additionally derives an all-radius windowed driver
and a source-style asymptotic wrapper, retaining its explicit model inputs.
The all-vertex two-term `hgap` was subsequently refuted under the stated
Case-3 growth inputs: `QZeroDiagonal` instead proves an exact root-obstruction
and a root-split repaired window sum. The off-diagonal estimate remains the
genuine target, still under its other hypotheses. See
[the Case-3 numerator note](docs/CRITICAL_LRP_CASE3_NUMERATOR.md) and
[the root-obstruction note](docs/CRITICAL_LRP_QZERO_DIAGONAL.md).
`QZeroReduction` adds conditional conversion/absorption and translation
invariance; `QZeroTransfer` proves exact finite-label and finite-cluster
restriction suprema for the star. Neither supplies the missing tree bound;
small-two-point/additive repairs remain open. See
[the transfer note](docs/CRITICAL_LRP_QZERO_TRANSFER.md). `QZeroRestoration`
adds exact restored/joint identities; `QZeroRepair` proves a vertexwise Harris
bound and its near-vertex obstruction; `QZeroMarked`/`QZeroAtlas` preserve
conditional residuals; `QZeroConsumer` handles exact sums and conversions.
None proves the old hgap, and the candidate target needs a small-two-point or
additive restriction. See [the restoration/diagram note](docs/CRITICAL_LRP_QZERO_DIAGRAMS.md).
`QZeroAtlas` proves the four shape evaluations and identifies `kpow=Kpow`;
`QZeroCount` derives the fifteen-representative recursion and its $(3,6,6)$
path classes; `QZeroStarAtlas4` realizes the canonical four-label event;
`QZeroRepairAudit` proves the exact covariance/additive reduction. The second
star's two-term estimate, its covariance bound, the remaining model inputs,
and I.4.20 stay open. See [the supporting-lemma note](docs/CRITICAL_LRP_ATLAS_SUPPORT.md).
`SecondMomentCase1` gives the mixed fourth-moment/case-specific rate assembly,
including E2 log-integrability and derived E0 log-integrability, with radial
regularity, hP, error measurability and p2H log-integrability retained.
`SecondMomentMeasurability` uses strict dyadic right-approximants to prove
the derivative weight and both error functions measurable from tail second-moment
finiteness; it also removes those measurability premises from the wrappers.
`FirstMomentLogError` derives the normalized first-moment log-error and the
`hP`, `hlogH`, `hlogE0` inputs from the landed corner-safe ODE machinery,
retaining its explicit kernel-tail, divergence, finiteness and continuity
inputs; its payoff wrapper still requires the refuted `hcase3`.
`SecondMomentTail` proves equivalence between interval-FTC data and
second-moment AC/a.e. differentiation. `OffCornerIdentity` now produces that
identity on off-corner windows from second-moment finiteness at the endpoint,
using the actual fixed-radius convergence theorem. `SecondMomentAllWindowAe`
removes the off-corner restriction from the a.e. derivative by a countable
rational-window cover. `SecondMomentPrimitiveConsistency` and
`SecondMomentCornerIdentity` further extend the integrated identity across
finitely many corners: the moment minus its interval primitive is continuous
and locally constant off the corner set. This supplies interval AC and the
consumer's a.e. derivative without asserting differentiability at attained radii.
`SecondMomentCornerSharpness` records why continuity and a.e. quantification
are essential. Tail second-moment finiteness and the edge-exhausting family
remain explicit; general I.4.15 and I.4.20 are not completed by these results.


`SecondMomentCase3.CriticalVolumeTail.UniformCutoff` expresses the uncut
critical-tail leaf as one radius-uniform cutoff tail, without constructing its
constant. `I420Case3.HDClosure` uses HD(3) in the actual higher-moment
interfaces, while `QZeroRepairAudit.Diagonal` proves the sharp diagonal
covariance instance and not the off-diagonal bound. See [the dependency-closure
note](docs/CRITICAL_LRP_HD_DEPENDENCY_CLOSURE.md). The independent
[HD/HD+ regime audit](docs/CRITICAL_LRP_REGIME_AUDIT.md) records exact case
boundaries and RV index algebra, not a critical HD(3) instantiation.

`TriangleFromHD.LargeDistance` makes the source's actual large-distance HD(3)
input explicit and constructs a normalized-norm counterexample to its literal
short-distance reading. `SecondMomentCase2.Source` proves the Case-2 error bound
with its tightness constant, retaining the mixed sixth-moment inequality.
`CornerContinuity` proves selected coefficient discontinuities and isolates the
uniform window tail needed for the full continuity premise. See their notes:
[large-distance HD(3)](docs/CRITICAL_LRP_HD3_LARGE_DISTANCE.md),
[Case 2](docs/CRITICAL_LRP_CASE2_SOURCE.md), and
[radial corners](docs/CRITICAL_LRP_RADIAL_CORNERS.md).

`SecondMomentCase2.RegularVariation` subsequently proves Case 2's regular
variation of index 3α from its sixth-moment input and the radius identity,
and distinguishes it from the positive limit requiring logarithmic error
integrability. It also provides a scalar ODE example showing why regular
variation alone does not imply a positive limiting constant.

The reviewed follow-up packet adds exact spatial-moment convergence, the
explicit I.1.7 chi-squared tail under its actual hypotheses, a conditional
pinned-star/covariance reduction, a log-free marginal-convolution obstruction,
and a conditional Case-1 `hHlog` measurability producer, as well as
second-moment lower-tail tools with a conditional $n^{-1}$ bound. The details and
remaining hypotheses are in the
[application packets note](docs/CRITICAL_LRP_APPLICATION_PACKETS.md). In
particular, weak convergence, restoration, the critical moments, and the
underlying two-point/covariance inputs are still open. The I.1.14 definition is
now classified FULL; this does not claim an unconditional Hydro model theorem.
`Tightness/I215` subsequently proves both cutoff and uncut median clauses of
I.2.15 from the named I.2.13 spatial-average hypothesis. The
[median application note](docs/CRITICAL_LRP_APPLICATION_PACKETS.md) records
those bounds and the single-branch exact evaluation, which is not a certified
replacement cover for the sixth mixed moment. See also the
[tail comparison note](docs/CRITICAL_LRP_TAIL_COMPARISON.md) for the exact
external two-intensity and susceptibility inputs, and
[the seven-point arm realization](docs/CRITICAL_LRP_APPLICATION_PACKETS.md)
handling collapsed terminals. The bipartite-class/mass evaluation remains open.
`Analysis/ClusterVolumeTail/AllOrderMomentsHconv` derives the I.1.7 weak
convergence from explicitly assumed all-order moment asymptotics; those
moments are not supplied. See `docs/CRITICAL_LRP_MOMENT_CONVERGENCE.md`.
`docs/CRITICAL_LRP_RANDOM_AMALGAM.md` records the self-determined random-family
amalgamation and the still-general decision-tree gap.
`docs/CRITICAL_LRP_CASE1_SINGLE_CLUSTER_TAIL.md` records the subsequent complete
proof of the single-cluster tail from finite first cutoff moments, and
`docs/CRITICAL_LRP_CASE1_TAIL_SCALE.md` retains its less complete precursor.
`docs/CRITICAL_LRP_DECISION_TREE_AMALGAM.md` proves the finite procedural
transcript/reconstruction lemma; it does not claim the full Gladkov inequality.
The [entropy core](docs/CRITICAL_LRP_ENTROPY_CORE.md) proves finite normalization,
log-sum, and sharpened Pinsker ingredients for the cited two-intensity argument.
`Correlation/I411/RowSum` proves the I.4.11 summation step, including its
countable extended-real form; its [row-sum note](docs/CRITICAL_LRP_I411_ROW_SUM.md)
keeps the two-copy numerator gap explicit as remaining work.

The next integration batch adds exact sixfold Tonelli/slot computations and an
explicit counterexample to the inadequate two-hub sixth-moment cover
([sixth-moment note](docs/CRITICAL_LRP_SIXTH_MOMENT_COVER.md)), exact displacement
and gyration-moment identities
([spatial-moment note](docs/CRITICAL_LRP_GYRATION_MOMENTS.md)), the exact binary
tree critical point ([tree note](docs/CRITICAL_LRP_BINARY_TREE_CRITICAL.md)),
and conditional singleton-flux discontinuities
([corner note](docs/CRITICAL_LRP_CORNER_FLUX.md)). Tail bounds from finite
moments remain per-radius estimates
([tail/second-moment note](docs/CRITICAL_LRP_TAIL_SECOND_MOMENT.md)).
`Analysis.Case3Hydro` proves the HD(3) and HD(2, α > 2)
hydrodynamic implications with their critical two-point hypotheses explicit
([Hydro note](docs/CRITICAL_LRP_HYDRO.md)). The
[source-fidelity audit](docs/CRITICAL_LRP_FIDELITY_AUDIT.md) records ten
independent checks, the I.1.6/I.4.15 normalization difference, and the
higher-moment closure from large-distance HD(3). None of this discharges the
sixth mixed tree/BK inequality, the critical tail, or the canonical-model
inputs.

No claim is made here that continuation-branch CI or every open source lemma
has passed. The current ledger records 20 FULL, 43 PARTIAL, and 12 NOT FORMALIZED numbered
items. The change also corrects the former I.4.12 classification: the repaired
`disjSet` theorem is not the source `apartSet` statement.
