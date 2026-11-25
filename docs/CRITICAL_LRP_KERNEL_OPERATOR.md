# Schur kernels and two-point operator algebra

`Analysis/KernelOperator/Defs.lean` introduces generic kernel application,
Schur row bounds, and PSD/composition structures. `Schur.lean` and
`Operator.lean` prove weighted Cauchy–Schwarz, square-summability bounds,
composition/associativity, translation invariance, positivity, and a conditional
third-power identification. `Model.lean` identifies the actual cutoff two-point
kernel with these interfaces under finite first cutoff mass `χ`.

The Schur row bound is the cluster mean, not the diagonal. The `toReal` encoding
pitfall is proved explicitly: an `ℝ≥0∞` row sum equal to `⊤` can have zero real
sum, so real-valued infinite-row bounds cannot detect that divergence.

The older third-power statement retains a Schur hypothesis on the composed
kernel. The additional modules `SchurComp.lean`, `LpOperator.lean`,
`InnerProduct.lean`, `CutoffComp.lean`, and `Composition.lean` now discharge
that hypothesis. `schurKernel_kernelComp` and `schurKernel_kernelCube` prove
it directly from one ordinary Schur hypothesis, and `kernelCLM` packages the
action as a bounded self-adjoint `ContinuousLinearMap` on real `ℓ²`, with norm at
most the row-sum bound. The composition and third-power identities are also
proved without the old extra composition premise.

The cutoff model instance still requires a finite first cutoff mean, since the
uncut critical row diverges and its real encoding alone is uninformative. There
is no positivity from arbitrary `IsPSDKernel`, no real continuous-functional-
calculus square root, and no Kozma model factorization yet. Those remain
separate tasks from the now-established Schur operator algebra.
