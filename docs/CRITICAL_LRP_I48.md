# Continuation: the analytic part of Corollary I.4.8

Source: supplied PDF, Corollary I.4.8 on page 37. This module does **not**
upgrade the source corollary to FULL.

`VolumeMoments/FirstMoment/CorollaryI48.lean` proves the scalar deduction
whose cutoff-model inputs had previously been left implicit. The main export
`first_moment_liminf_lower_bound_critical` takes a positive differentiable
function `F` on a tail, `F → ∞`, and the ODE

```text
F'(r) = (1 - E₁,r) (1 - E₀,r) βc r^(-α-1) F(r)^2.
```

It proves the liminf conclusion in the equivalent eventual formulation: for
every `c < α/βc`, eventually `c r^α ≤ F r`. The theorem
`first_moment_liminf_rpow_lower_bound_critical` gives the equivalent statement
with `r^(-α) F r` on the right. No measurability or boundedness of the error is
needed. In particular, this deduction does not use the exact integral identity
from Lemma I.4.5(3).

The sign argument is explicit:

```text
0 ≤ E₁  and  0 < 1 - E₀  ⟹  (1 - E₁)(1 - E₀) ≤ 1 - E₀.
```

The generic theorem `first_moment_liminf_lower_bound` accepts an error bounded
below by `-ε` eventually for every positive `ε`. It covers strictly negative
errors, as witnessed by `first_moment_liminf_lower_bound_negative_error_witness`.
There is no attempt to derive the bound by assuming the error is nonnegative.

`oneSubE0_tendsto_one` proves the other asymptotic input. In the normalized
power-law form `|J'(r)| = (1 + δr) r^(-d-α-1)`, with `δr → 0` and positive
dimension, it uses `lemma_I_4_6_isEquivalent` to prove
`|J'(r)| |B_r| r^(α+1) → 1`.

## What remains open

The cutoff first moment must still be identified as a real differentiable
function of the radius with this ODE. The newer `CriticalLRP/CutoffLimit` result
now proves monotone convergence of the extended cutoff first moment to the
uncut mean, including divergence when the uncut mean is `⊤` as an explicit
premise. This settles the extended limit, not differentiability or a finite
real-valued assertion, and it does not discharge the uncut infinite-mean input.
The finite critical first-moment premise feeding nonnegativity of `cE1` also
remains open for the intended model. The source conclusion is therefore
represented by a proved analytic component and exposed model obligations,
rather than by an unconditional instantiation of the infinite cutoff model.

## Validation

On the uncommitted integration worktree based at `c0f85e4`, the module passed
focused compilation and then the full `lake build --wfail PercLib` build of
9,474 jobs. Import closure covered 427 modules. The ten focused `#print axioms`
checks, including both witnesses, use only `propext`, `Classical.choice` and
`Quot.sound`. These are local checks on the candidate revision, not CI results.
