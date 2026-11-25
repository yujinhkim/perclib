# Positivity of the cutoff two-point operator

`Analysis/KernelOperator/CutoffPositivity/`, accepted from follow-up swarm `smwtxo95t` member `m6`, proves nonnegative quadratic and cubic forms for positive-semidefinite Schur-kernel operators and instantiates them at the actual range-truncated two-point law.

The abstract proof computes the quadratic form as the lattice sum of the kernel double family. Summability follows from the existing Schur estimates. Finite square blocks are nonnegative by `IsPSDKernel` and are cofinal among finite subsets of the product type, so their nonnegativity passes to the full sum. The cubic form uses self-adjointness and quadratic-form positivity of the transformed vector. `kernelComp_isPSDKernel` holds from Schur data alone, while `kernelCube_isPSDKernel` uses positivity of the original kernel.

At the cutoff, `cutKernel_isPSDKernel` comes from the finite-matrix positivity of the actual truncated connection probabilities. At a finite first cutoff moment, `cutKernelCLM_quadForm_nonneg` and `cutKernelCLM_cube_form_nonneg` give the operator-level positivity, and `cutKernelCLM_norm_le` retains the first-moment Schur bound. The two- and three-step cutoff kernels are also positive semidefinite. The CFC theorem additionally requires a self-adjoint complex extension as an explicit input.

Finite first moment is not inferred at arbitrary large radius. `not_schurKernel_of_cutMassAt_eq_top` shows why it is necessary: if the cutoff mass at one vertex is `⊤`, there is no Schur constant at all and the bounded operator cannot be formed. No critical Schur bound, critical bounded operator, limit-law positivity, `B^3 = openTriangle`, or Kozma theorem is claimed.
