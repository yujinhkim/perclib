# Case-3 numerator: the false pointwise `hT3` and the proved repairs

## Status at a glance

The old case-three interface is not merely missing a proof of `hT3`; its
uniform pointwise estimate is incompatible with the vanishing driver. This
makes the old `secondMoment_asymptotic_case3` hypothesis bundle uninhabited
under its ordinary finite-moment hypotheses. **That does not refute
Proposition I.4.15.** It shows that a different numerator consumer is needed.

Four independently checked developments now address different parts of that
problem:

1. the exact `q = 0` identification of the per-vertex numerator;
2. a summed near/far replacement for `hT3`, including its driver asymptotics;
3. an alternative marked-polynomial bound whose residual is explicit; and
4. a derived near-count consumer and logarithmic-integrability proof.

The actual two-term `p = 3, q = 0` tree-count estimate (`hgap`) remains open.
Several of the remaining probabilistic inputs—triangle/tail conditions,
moment gaps, finitude and radius measurability—are still explicit hypotheses
of the relevant theorems. No general Proposition I.4.15 or I.4.20 is claimed.

## 1. Why the old bundle is uninhabited

For finite cutoff first moments, the threefold cutoff two-point power obeys
`1 ≤ polyK (M.cutTwoPoint r) 3 0 0`. But the old hypothesis is
`∀ r ≥ 1, ∀ y, polyK (M.cutTwoPoint r) 3 0 y ≤ Cp * case3Driver c r`,
with `Cp * case3Driver c r → 0`. Choosing `y = 0` contradicts that limit.

Proved independently in:

* `Analysis.SecondMomentCase3.SummedThree.Obstruction`
  (`not_forall_polyK_three_le_case3Driver`);
* `Analysis.SecondMomentCase3.EllThreeObstruction`
  (`not_exists_case3_hypothesis_bundle`, also `_of_cutMoment_two`); and
* `Analysis.SecondMomentCase3.ConsumerGap`
  (`not_pointwise_polyK_three_of_driver_tendsto_zero` and
  `hcase3_unsatisfiable`).

The printed Lemma I.4.18 has the same diagonal problem at `ell = 3`. This is
a source-scope/proof-availability discrepancy, not an assertion that the whole
second-moment proposition is false. The old conditional wrapper remains in the
tree as a historical conditional statement, not as a non-vacuous Case-3 proof.

## 2. The exact `q = 0` object and the failed marked-family specialization

`Correlation.I417.General.QZeroStar` defines the single-copy star moment
`starMoment π x y p = E[1(x ↔ y) |K_x|^p]` and proves:

* the exact disconnected-plus-connected additive identity, with finite
  subtractive and real forms;
* the labelled expansion as a one-copy `(p+1)`-point event; and
* equality with the literal `connCubeVertexMass r y` at `p = 3` in the cutoff
  model, and with the window sum.

The general marked family is indexed by `Fin q × V`, hence is zero at `q = 0`.
Its strict inequality against a positive star moment is
`markedFamily_q_zero_lt_starMoment`. Thus the previous two-copy marked-family
expression cannot simply be specialized at `q = 0`.

What remains is the expected one-copy tree estimate:

```
starMoment (M.cutProb r) 0 y 3
  ≤ C₃ * T³(0,y) * χ⁴ + C₄ * T⁴(0,y) * χ³,
```

with its seven-edge expansion and the `ell = 3` and `ell = 4` diagram counts.
The new bridge does not prove that inequality.

The exact `p = q = 0` evaluation also records why the printed display needs a
nondegenerate scope condition. That separate degenerate case does not affect
`p = 3, q = 0`.

## 3. Summed near/far `ell = 3`: `SummedThree`

`Analysis.SecondMomentCase3.SummedThree` replaces the pointwise hypothesis by
an actual window sum. Its `Defs.lean` defines

```
case3ThreeDriver s θ r
  = (nablaTail (r^θ)).toReal + (|s r| / |B_r|) * triSelf.
```

`sum_polyK_three_ballF_le_near_far` applies the landed
`I420Case3.sum_polyK_three_le_near_far` at the actual `ballF` window. A near
family with distance at least `r^θ` outside it yields

```
∑_{y∈B_r} T³(0,y) ≤ |B_r| * case3ThreeDriver s θ r.
```

`connCubeMass_toReal_le_of_nearSets` and
`connCubeMass_le_of_source_threeDriver` therefore retain the exact per-vertex
`hgap` and `hpoly4`, but no pointwise `hT3`. Near sets of size at most
`K r^{θd}` are constructed with the landed lattice near-ball theorem.

For `0 < θ < 1`, the driver tends to zero and is logarithmically integrable:
the far term uses the open-triangle tail, and the near ratio is dominated by
`K 2^d r^{-(1-θ)d}`. `logIntegrable_p2ExclError_of_source_split` carries these
through the second-moment error algebra.

The remaining hypotheses include `hgap`, `hpoly4`, `hTri`, the real-valued
`nablaTail` log-error input, `hgm`, finite cutoff/window moments, and radius
measurability of the driver and `p2ExclError`. None of those is invented or
silently discharged.

## 4. Alternative marked bound: residual and limits

`Analysis.SecondMomentCase3.MarkedPolygon` gives another proof that
`connCubeVertexMass = I417Gen.jointPow`. The landed marked bound then applies
for all `p`, at `p = 3` yielding a polynomial bound over **`ell = 1,2,3,4`**,
not the source `hgap` with only `ell = 3,4`.

After exact real column sums, the numerator bound is

```
C_low * χ⁷ + markedCount 3 4 * Cp * |B_r| * drv * χ⁴,
```

and the error estimate retains the corresponding
`χ³ / |B_r|` residual. `exists_connCubeMass_toReal_le_markedPolygon` discharges
`hpoly4` using the landed all-radius theorem, retaining finiteness and the
first-moment/triangle inputs.

`connCubeMass_toReal_le_of_chi_cube_le` and
`p2ExclError_tendsto_zero_of_markedPolygon` show vanishing only under the
additional explicit residual condition `χ³ ≤ K |B_r| drv`, together with the
usual moment gap and driver vanishing. This is not a proof of the exact
source `hgap`, nor a proof that its new scalar condition holds in general Case
3.

`Analysis.SecondMomentCase3.EllThreeObstruction` independently gives the
lossy direct column-sum bound and the residual divergence/decay statements:
the upper-bound residual grows in `d < 3α` and vanishes in `3α < d`, with the
source first-moment asymptotic and lattice-ball geometry retained. The
resulting `tendsto_p2ExclError_zero_of_case1` is conditional on `hgap`,
`hpoly4`, `hgm`, `hP`, driver vanishing and finiteness. None of this proves
that `E_{2,r}` itself diverges in Case 3.

## 5. Derived near-count consumer: `ConsumerGap`

`Analysis.SecondMomentCase3.ConsumerGap` gives the independent exact consumer
form. `polyK_three_window_budget` obtains

```
∑_{y∈B_r} T³(0,y)
  ≤ triSelf * N_R + |B_r| * (nablaTail R).toReal,
```

and `nearFilter_card_le_ball_ncard` and `exists_nearCount_bound` establish
`N_{r^c} ≤ Kc r^{c d}` from `ball_count`, with no separate near-count input.

The central `p2ExclError_le_case3_of_tri` then produces the required driver
plus the near-count ratio from the actual `hgap`, `hpoly4`, `hgm` and finite
moments. For `0 < c < 1`, this ratio is logarithmically integrable and tends
to zero. Its exact generic repaired conclusions are
`p2ExclError_tendsto_zero_of_case3_repaired` and
`logIntegrable_p2ExclError_of_case3_repaired`, with their hypotheses preserved.

`columnResidual_not_tendsto_zero` proves the stronger limitation
`3α ≥ d` for the classical column-sum residual: it cannot vanish under the
first-moment asymptotic and `ball_count`. This is a no-go theorem for the
column-sum substitute, not for the repaired near/far route or Proposition
I.4.15.

## 6. First-moment inputs: `FirstMomentLogError`

`isLogErrorFunction_cutE0` packages the standardized error. The new
`isLogErrorFunction_one_sub_mul_of_eventually` makes the needed correction
from a global to an eventual bound when composing `1-(1-E0)(1-E1)`.

Using the established corner-safe cutoff ODE/AC and log-error analysis,
`isLogErrorFunction_p2H` proves that the actual normalized first-moment error
is logarithmically integrable and tends to zero. `tendsto_cutMassRatio`,
`logIntegrable_cutE0'` and `case3_firstMoment_inputs` discharge the `hP`,
`hlogH` and `hlogE0` assumptions of the conditional second-moment wrappers.
A triangle-condition form supplies `E1` using the landed cut-defect theorem.
The stated kernel-tail, positivity, divergence, finite-moment and continuity
inputs are retained.

Its `secondMoment_asymptotic_case3_of_firstMoment` still requires the old,
separately uninhabited `hcase3`, so it is not evidence that Case 3 has been
completed. The usable subsequent assembly must compose these first-moment
results with one of the proved repaired consumers.

Principal supporting note: `docs/CRITICAL_LRP_I417_QZERO.md`.
Every listed submission was independently elaborated with strict Lean flags
and its exports were audited to use only `propext`, `Classical.choice`, and
`Quot.sound`.
