# The hydrodynamic condition for HD(3) and HD(2) with α > 2

`Analysis/Case3Hydro.lean` proves Corollary I.4.14 for its two-point alternatives
(3), and (2) when `α > 2`. It does not create or instantiate those critical
estimates and does not address Case 1.

For Definition I.1.14 itself, `Orchestration/Defs.lean` already supplies
`SourceModelData.Mr` as the natural-number infimum of the stated median event,
and `SourceModelData.Hydro` as
`M_r / r^((d+α)/2) → 0`. This agrees with the paper's minimum over `n ≥ 0`
under the normalized-window cutoff law. The earlier NOT FORMALIZED definition
entry was stale. Its correction concerns the predicate, not a claim that the
canonical model has been shown to satisfy Hydro in all three cases.

## The model's own normalized-ball averaging

The proof defines `ballAt x s`, the closed source-norm ball centred at `x`,
and shows it is translation invariant. The configuration shift preserves both
the cluster and the normalized source ball, so the same event probability is
independent of `x`.

`winCount` counts points whose own cluster meets the prescribed size in its own
doubled window. The counting argument, midpoint/cluster equivalence and exact
expectation yield the averaging input needed for the median step. The actual
median `M.Mr` is identified with production's edian of the largest cluster in a
closed ball.

That leads to `mr_sq_le_inter`: for every nonnegative radius,

```text
(M_r - 1)^2 ≤ e · |B_r| · E_{β_c,r}|K ∩ B_{2r}|.
```

The point is the *windowed* first-moment bound, not an unavailable bound on the
full critical moment. `lintegral_clusterVolIn_ball_eq_sum` converts that
windowed moment exactly into a two-point sum; cutoff domination then bounds it
by the uncut two-point sum.

## Logarithmic and log-free summation

`sum_tau_ball_le_of_case3` applies production's normalized ball-shell estimate
to the positive-log two-point majorant supplied by literal HD(3), giving a
bound of order `r² / log r`. The logarithm in HD(3) supplies precisely the
missing gain at the hydrodynamic exponent.

The median bound is correspondingly

```text
(M_r - 1)^2 ≤ C · r^(d+α) / log r,
```

and `hydro_of_case3HD` and `mr_le_rpow_log` give `Hydro` and a quantitative
half-power-logarithmic estimate. The same conclusion is available as
`hydro_of_case3HDLarge`, through the positive-log majorant equivalent to
`Case3HDLarge`. No near-origin use of the totalized inverse logarithm is needed.
The HD and HDplus wrappers are included but supply no critical estimate
themselves.

For HD(2), the log-free pointwise profile gives the ball sum of order `r²`, and
the median-squared bound of order `r^(d+2)`. The strict range `α > 2` gives
`(d+2)/2 < (d+α)/2`, hence `hydro_of_case2`. At `α = 2` this computation alone
would be marginal, not a proof of Hydro. Case 1 needs its own ODE/bootstrap
route and is not covered here.

## Recorded source normalization discrepancy

The supplied PDF's proof of Corollary I.4.14 prints a factor `r^{-d}` in its
median step whereas the next line's summed two-point estimate requires `r^d`.
The reconstruction uses the positive exponent appropriate to the windowed
median estimate. This is not silently rewritten as a faithful copy of the
printed display, nor is it used to claim a source-wide hydrodynamic theorem.

The companion `Tightness/I215` proves both the cutoff and uncut median bounds
from the explicit Theorem-I.2.13 hypothesis `SpatialTwoPointAverage`. Its
uncut proof separately verifies translation invariance and the same positive
window normalization; the "In fact" uncut clause is therefore included rather
than omitted. The cited two-point estimate remains the remaining input.

## Residual scope and validation

No perturbative or lace-expansion result is supplied. The input statements in
HD(3) and HD(2) remain critical two-point hypotheses. There is no degenerate
zero-intensity instantiation, no finite-volume substitute for the actual cutoff
lattice, and no unconditional model coverage.

All 34 reported proof axioms are standard. `Hydro.lean` is the integrated
package; the older `Defs.lean`/`Window.lean` development artifacts are not
duplicated in production. The focused build and full production validation both
cover it.
