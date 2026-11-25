# CFC square roots and the real/complex `ℓ²` bridge

`Analysis/KernelOperator/CFC/Defs.lean` defines `CFC.sqrtCube`, the nonnegative square root of a cube in a unital C⋆-algebra, and `Realification.ofRealLp`, the embedding of real-valued `ℓ²` into complex-valued `ℓ²`. `Analysis/KernelOperator/CFC.lean`, accepted from swarm `smwtvrwnn` member `m7`, supplies the proofs.

For `0 ≤ B`, `S = CFC.sqrtCube B` is nonnegative and self-adjoint, satisfies `S† * S = B^3`, and agrees with the CFC `3/2`-power. The package proves uniqueness and, for operators on a complex Hilbert space, the Gram identity `⟪B^3 f, g⟫ = ⟪S f, S g⟫`. The nonnegativity premise is essential: `CFC.sqrt` alone does not justify the square identity for a non-positive input.

The realification layer expands inner products under an explicit real structure, proves the real/imaginary decomposition of complex `ℓ²`, transports self-adjointness and positivity, and identifies powers of a complexified real operator. `exists_sqrt_cube_real_operator` combines these facts: given a real `ℓ²` operator `T`, a self-adjoint complex extension `Tℂ`, and nonnegative real quadratic form, it produces a complex nonnegative self-adjoint `S` with `S† * S = Tℂ^3` and the corresponding real-vector Gram identity.

The complex extension and positive-semidefinite quadratic form are still inputs, not consequences of Schur bounds. This is not a real-valued square-root descent theorem and does not construct the critical two-point operator, prove its boundedness or positivity, identify `B^3` with `openTriangle`, or complete Kozma's factorization.
