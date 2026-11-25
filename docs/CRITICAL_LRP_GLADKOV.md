# Conditional Gladkov mixed-moment bound (I.2.8)

`CriticalLRP/Correlation/Gladkov.lean` proves Corollary I.2.8 from the exact
Gladkov inequality. The user explicitly allowed that inequality to be assumed
for now. It is represented by `GladkovInput`, not by a custom axiom and not by a
standalone proof of Theorem I.2.7.

## Main statement

For native Bernoulli bond percolation on a countable vertex type, suppose
root independence holds:

```text
∀ z, chi π z = chi π x
```

and `input : GladkovInput π x` supplies

```text
∀ y z, law π (conn x y ∩ conn x z)^2 ≤
    8 * law π (conn x y) * law π (conn y z) * law π (conn z x).
```

Then `mixed_moment_le_of_gladkov` proves, for every finite window `W`,

```text
E[|K_x| |K_x∩W|] ≤ 8^(1/2) (E|K|) * (|W| E|K_x∩W|)^(1/2).
```

The whole unwindowed mean is outside the second square root. `gladkov_constant`
proves `8^(1/2) = 2^(3/2)`, so this is the source's `2^(3/2)` prefactor. This
parenthesization was checked against the rendered supplied PDF page 24 rather
than the extracted radical grouping.

No finiteness premise on the full mean is introduced. All inequalities,
indicator expansions and Cauchy–Schwarz steps are in `ℝ≥0∞`, including
infinite values; there is no `toReal` conversion of an unbounded mean.

## Proof composition

* `inner_sum_bound` takes half-powers of the exact squared Gladkov input and
  applies Cauchy–Schwarz over `y`.
* `window_sum_bound` reorders the two sums and applies Cauchy–Schwarz over the
  finite window, producing exactly the square root of the window cardinality
  times the expected window volume.
* `lintegral_cluster_mul_inter_eq_tsum` identifies
  `E[|K_x| |K_x∩W|]` with the double sum of joint connection probabilities.
* `lintegral_cluster_inter_eq_tsum` gives the separate expected window volume
  used in the second Cauchy–Schwarz step.
* Root independence identifies every full mean with `chi π x`. The Tonelli
  identity `chi_eq_tsum_tau` turns these into the row sums used in the scalar
  bound. Compared mean roots and connection symmetry are explicit; this is not
  inferred from a homogeneous second-moment estimate.

The module also exports `mixed_moment_le_of_gladkov_cutoff`. This uses the
loop-safe `CutoffKernel.cutoffSymKernel` model and proves root independence
from `CutoffKernel.cutoffSymKernel_shift` and `Hvol.hvol_cardFun`.
Compatibility with the native bond law is via `edgeMeasure_eq_law`. Thus the
intended cutoff family does not need an additional root-independence premise.

## Input status and non-vacuity

`Correlation/Gladkov/Defs.lean` defines `GladkovInput`, with the exact source
three-point statement as its only field. Its singleton witness proves the
input is inhabited: on a one-vertex model, self-connection has measure one
regardless of the diagonal pair's probability. The source reference and
remaining proof obligation are listed in `docs/CITED_INPUTS.md`.

Nothing here proves the finite decision-tree argument underlying Gladkov's
theorem or its infinite-volume limiting step. The status of I.2.7 is
therefore not upgraded as a proved source theorem. I.2.8 is PARTIAL because
its remaining explicit input is precisely I.2.7. Higher-k and four-point
Gladkov inequalities remain outside this module's scope.

This work also does not complete I.4.9, sharpness, a finite-mean bootstrap at
criticality, triangle finiteness, or the cutoff derivative. Extended-real
mean bounds do not silently become statements of finite susceptibility.
