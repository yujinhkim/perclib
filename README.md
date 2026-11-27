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
`SecondMomentCase3` also gives the conditional Case-3 numerator/ratio
assembly and second-moment asymptotic, with the p=3,q=0 numerator gap,
ell=3 input, radial regularity and critical volume-tail still explicit.
These do not supply all remaining model data.


No claim is made here that continuation-branch CI or every open source lemma
has passed. The current ledger records 19 FULL, 42 PARTIAL, and 14 NOT FORMALIZED numbered
items. The change also corrects the former I.4.12 classification: the repaired
`disjSet` theorem is not the source `apartSet` statement.
