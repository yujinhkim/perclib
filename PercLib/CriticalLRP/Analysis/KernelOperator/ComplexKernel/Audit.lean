/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Consolidated axiom audit for the complex kernel operator package.

Swarm `smwtxo95t`, member `m1`, direction (D) "concrete complex kernel operator".

Every declaration of the package is listed; each must depend only on `propext`,
`Classical.choice` and `Quot.sound`.  There must be no `sorryAx`, no `native_decide`, and no
custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.Nonvacuity.Basic
public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.Obstruction.Basic

/-!
# Axiom audit for the complex kernel operator package
-/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.KernelOperator

-- definition
#print axioms kernelApplyℂ

-- construction and Schur bound on complex `ℓ²`
#print axioms summable_norm_sq_of_memℓp
#print axioms summable_row_mul_complex
#print axioms norm_kernelApplyℂ_le_kernelApply_norm
#print axioms tsum_sq_kernelApplyℂ_le
#print axioms memℓp_kernelApplyℂ
#print axioms kernelLpℂ
#print axioms kernelLpℂ_apply
#print axioms kernelLpℂ_add
#print axioms kernelLpℂ_smul
#print axioms kernelLinearMapℂ
#print axioms kernelLinearMapℂ_apply
#print axioms kernelLpℂ_norm_sq
#print axioms lp_norm_sq_complex
#print axioms kernelLpℂ_norm_le
#print axioms kernelCLMℂ
#print axioms kernelCLMℂ_apply
#print axioms kernelCLMℂ_norm_le
#print axioms kernelCLMℂ_apply_eq_tsum

-- agreement with the real operator
#print axioms kernelApplyℂ_ofReal
#print axioms kernelLpℂ_ofRealLp
#print axioms kernelCLMℂ_ofRealLp

-- self-adjointness, uniqueness, composition and powers
#print axioms isSelfAdjoint_kernelCLMℂ
#print axioms kernelCLMℂ_adjoint
#print axioms inner_kernelCLMℂ_comm
#print axioms eq_kernelCLMℂ_of_agrees_on_real
#print axioms kernelCLMℂ_mul_self
#print axioms kernelCLMℂ_pow_ofRealLp
#print axioms kernelCLM_pow_three_apply
#print axioms kernelCLMℂ_pow_three_apply
#print axioms kernelCLMℂ_pow_three_eq

-- the CFC square root of the `openTriangle` operator
#print axioms inner_pow_three_eq_tsum_kernelCube
#print axioms exists_sqrt_cube_kernelCLM
#print axioms exists_sqrt_cube_kernelCLM_gram

-- non-vacuity
#print axioms oneKernel
#print axioms oneLp
#print axioms schurKernel_oneKernel
#print axioms kernelCLM_oneKernel_apply
#print axioms kernelCLM_oneKernel_eq_self
#print axioms inner_oneKernel_nonneg
#print axioms kernelCLMℂ_oneKernel_apply_one
#print axioms kernelCLMℂ_oneKernel_ne_zero
#print axioms exists_sqrt_cube_oneKernel

-- the Schur hypothesis does not imply positivity of the quadratic form
#print axioms offDiagKernel
#print axioms signLp
#print axioms schurKernel_offDiag
#print axioms kernelCLM_offDiag_apply
#print axioms inner_offDiag_signLp
#print axioms not_nonneg_offDiag

end PercLib.CriticalLRP.KernelOperator
