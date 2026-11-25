/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

A checked obstruction: the Schur hypothesis does not imply positivity of the quadratic form.

Swarm `smwtxo95t`, member `m1`, direction (D) "concrete complex kernel operator".

This is what makes the positivity hypothesis of `exists_sqrt_cube_kernelCLM` a real hypothesis
rather than a consequence of `SchurKernel`: the off-diagonal kernel on two points is a Schur
kernel with constant `1`, but its quadratic form at `(1, -1)` is `-2`.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.CFC
public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.Obstruction.Defs

/-!
# The Schur bound does not give positivity
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp InnerProduct InnerProductSpace

namespace PercLib.CriticalLRP.KernelOperator

/-- **The off-diagonal kernel is a Schur kernel with constant `1`.** -/
theorem schurKernel_offDiag : SchurKernel offDiagKernel 1 where
  nonneg := by
    intro x y
    rw [offDiagKernel]
    split <;> norm_num
  symm := by
    intro x y
    simp only [offDiagKernel, eq_comm]
  nonneg_A := zero_le_one
  row_summable := fun _ => Summable.of_finite
  row_le := by
    intro x
    rw [show (∑' y : Bool, offDiagKernel x y)
        = offDiagKernel x true + offDiagKernel x false from by simp]
    cases x <;> simp [offDiagKernel]

/-- The kernel operator of the off-diagonal kernel sends the vector `(1, -1)` to `(-1, 1)`. -/
theorem kernelCLM_offDiag_apply (x : Bool) :
    (kernelCLM schurKernel_offDiag signLp : Bool → ℝ) x = if x then -1 else 1 := by
  rw [kernelCLM_apply_eq_tsum]
  rw [show (∑' y : Bool, offDiagKernel x y * (signLp : Bool → ℝ) y)
      = offDiagKernel x true * (signLp : Bool → ℝ) true
        + offDiagKernel x false * (signLp : Bool → ℝ) false from by simp]
  cases x <;> simp [offDiagKernel, signLp]

/-- **The quadratic form of the off-diagonal kernel at `(1, -1)` is `-2`.** -/
theorem inner_offDiag_signLp :
    ⟪kernelCLM schurKernel_offDiag signLp, signLp⟫_ℝ = -2 := by
  rw [lp.inner_eq_tsum]
  rw [show (∑' x : Bool, ⟪(kernelCLM schurKernel_offDiag signLp : Bool → ℝ) x,
        (signLp : Bool → ℝ) x⟫_ℝ)
      = ⟪(kernelCLM schurKernel_offDiag signLp : Bool → ℝ) true,
          (signLp : Bool → ℝ) true⟫_ℝ
        + ⟪(kernelCLM schurKernel_offDiag signLp : Bool → ℝ) false,
            (signLp : Bool → ℝ) false⟫_ℝ from by simp]
  rw [kernelCLM_offDiag_apply true, kernelCLM_offDiag_apply false]
  simp only [real_inner_eq_mul, signLp]
  norm_num

/-- **Schur data alone does not give positivity.**  The off-diagonal kernel satisfies
`SchurKernel offDiagKernel 1`, yet its real quadratic form is not nonnegative, so the hypothesis
`∀ a, 0 ≤ ⟪kernelCLM h a, a⟫_ℝ` of `exists_sqrt_cube_kernelCLM` is not derivable from
`SchurKernel` and must remain an explicit input. -/
theorem not_nonneg_offDiag :
    ¬ ∀ a : lp (fun _ : Bool => ℝ) 2, 0 ≤ ⟪kernelCLM schurKernel_offDiag a, a⟫_ℝ := by
  intro h
  have h1 := h signLp
  rw [inner_offDiag_signLp] at h1
  norm_num at h1

end PercLib.CriticalLRP.KernelOperator

set_option linter.hashCommand false

/-! ### Axiom audit -/
#print axioms PercLib.CriticalLRP.KernelOperator.offDiagKernel
#print axioms PercLib.CriticalLRP.KernelOperator.signLp
#print axioms PercLib.CriticalLRP.KernelOperator.schurKernel_offDiag
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLM_offDiag_apply
#print axioms PercLib.CriticalLRP.KernelOperator.inner_offDiag_signLp
#print axioms PercLib.CriticalLRP.KernelOperator.not_nonneg_offDiag
