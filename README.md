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
item-by-item status and explicit open assumptions. Recent continuation results
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
for exact scopes. The older conditional Case-3 numerator/ratio assembly and
second-moment asymptotic remain available for the optional q-zero star route.
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


No claim is made here that continuation-branch CI or every open source lemma
has passed. The current ledger records 19 FULL, 42 PARTIAL, and 14 NOT FORMALIZED numbered
items. The change also corrects the former I.4.12 classification: the repaired
`disjSet` theorem is not the source `apartSet` statement.
