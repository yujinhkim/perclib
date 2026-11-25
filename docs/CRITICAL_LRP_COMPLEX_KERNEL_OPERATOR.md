# Concrete complex Schur-kernel operator

`Analysis/KernelOperator/ComplexKernel/`, accepted from follow-up swarm `smwtxo95t` member `m1`, constructs the complex counterpart of the bounded self-adjoint real Schur-kernel operator on `ℓ²` and retains the CFC interface.

For a real symmetric nonnegative `SchurKernel κ A`, `kernelCLMℂ h` is a genuine bounded complex-linear operator on complex `ℓ²`. Its kernel series is summable on every square-summable complex vector, and the operator norm is at most the plain real Schur bound `A`. The package proves the kernel formula, agreement with real `kernelCLM` on `ofRealLp`, self-adjointness, uniqueness of this complex-linear extension, the composition identity, real/complex power compatibility, and identification of the cube with the operator of `kernelCube κ`.

`exists_sqrt_cube_kernelCLM` combines this with the earlier CFC package: given nonnegative real quadratic form of `kernelCLM h`, it supplies a nonnegative self-adjoint `S` with `S† * S = kernelCLMℂ (schurKernel_kernelCube h)` and the corresponding real-vector Gram identity. The positivity premise is essential. `Obstruction/Basic.lean` gives a two-point Schur kernel of constant `1` whose quadratic form at `(1,-1)` is `-2`, so Schur bounds alone cannot establish it. `Nonvacuity/Basic.lean` verifies the complete square-root chain on the nonzero identity operator of the one-point lattice.

This is not a critical Schur bound, model positivity theorem, critical bounded two-point operator, or full Kozma factorization. The remaining model step is to instantiate the real cutoff positivity and identify the resulting cube-kernel operator with the paper's actual triangle operator.
