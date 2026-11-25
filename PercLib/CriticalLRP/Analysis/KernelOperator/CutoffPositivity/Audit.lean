/-
Axiom audit for the cutoff-positivity package.

Swarm `smwtxo95t`, member `m6`, direction (E).  Every declaration delivered by this package is
listed; the expected answer is `propext`, `Classical.choice`, `Quot.sound` only (no `sorryAx`).
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.CutoffPositivity.Composed
public import PercLib.CriticalLRP.Analysis.KernelOperator.CutoffPositivity.Obstruction

/-!
# Axiom audit for the cutoff-positivity package
-/

set_option linter.hashCommand false

/-! ### Definitions (axiom-free by construction, audited for completeness) -/

#print axioms PercLib.CriticalLRP.CutoffPositivity.QuadFormNonneg
#print axioms PercLib.CriticalLRP.CutoffPositivity.kernelForm
#print axioms PercLib.CriticalLRP.CutoffPositivity.cutKernelCLM

/-! ### Abstract Schur-kernel results (`Positivity/Basic.lean`) -/

#print axioms PercLib.CriticalLRP.CutoffPositivity.summable_kernelForm
#print axioms PercLib.CriticalLRP.CutoffPositivity.inner_kernelCLM_eq_kernelForm
#print axioms PercLib.CriticalLRP.CutoffPositivity.tendsto_finset_prod_sq_atTop
#print axioms PercLib.CriticalLRP.CutoffPositivity.kernelForm_block_nonneg
#print axioms PercLib.CriticalLRP.CutoffPositivity.kernelCLM_quadForm_nonneg
#print axioms PercLib.CriticalLRP.CutoffPositivity.kernelCLM_adjoint
#print axioms PercLib.CriticalLRP.CutoffPositivity.kernelCLM_cube_form_nonneg

/-! ### The cutoff two-point instantiation (`Positivity/Cutoff.lean`) -/

#print axioms PercLib.CriticalLRP.CutoffPositivity.cutKernel_isPSDKernel
#print axioms PercLib.CriticalLRP.CutoffPositivity.cutKernelCLM_quadForm_nonneg
#print axioms PercLib.CriticalLRP.CutoffPositivity.cutKernelCLM_cube_form_nonneg
#print axioms PercLib.CriticalLRP.CutoffPositivity.cutKernelCLM_adjoint
#print axioms PercLib.CriticalLRP.CutoffPositivity.cutKernelCLM_norm_le
#print axioms PercLib.CriticalLRP.CutoffPositivity.exists_sqrt_cube_cutKernelCLM

/-! ### Composed and cube kernels (`Positivity/Composed.lean`) -/

#print axioms PercLib.CriticalLRP.CutoffPositivity.kernelCLM_sq_apply_eq
#print axioms PercLib.CriticalLRP.CutoffPositivity.kernelCLM_cube_apply_eq
#print axioms PercLib.CriticalLRP.CutoffPositivity.inner_sq_eq_kernelForm
#print axioms PercLib.CriticalLRP.CutoffPositivity.inner_cube_eq_kernelForm
#print axioms PercLib.CriticalLRP.CutoffPositivity.memℓp_two_of_forall_notMem_eq_zero
#print axioms PercLib.CriticalLRP.CutoffPositivity.tsum_kernelForm_eq_sum
#print axioms PercLib.CriticalLRP.CutoffPositivity.kernelComp_isPSDKernel
#print axioms PercLib.CriticalLRP.CutoffPositivity.kernelCube_isPSDKernel
#print axioms PercLib.CriticalLRP.CutoffPositivity.cutKernel_comp_isPSDKernel
#print axioms PercLib.CriticalLRP.CutoffPositivity.cutKernel_cube_isPSDKernel

/-! ### Obstruction to an infinite cutoff moment (`Positivity/Obstruction.lean`) -/

#print axioms PercLib.CriticalLRP.CutoffPositivity.not_schurKernel_of_cutMassAt_eq_top
#print axioms PercLib.CriticalLRP.CutoffPositivity.not_schurKernel_of_cutMassAt_zero_eq_top
