
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.SchurComp
public import PercLib.CriticalLRP.Analysis.KernelOperator.LpOperator
public import PercLib.CriticalLRP.Analysis.KernelOperator.CutoffComp
public import PercLib.CriticalLRP.Analysis.KernelOperator.InnerProduct

/-!
Combined statements: the Schur kernel operator on `ℓ²` and the discharged composition
hypothesis.

Swarm `smwttizjk`, member `m2`, direction D6A.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*} {κ : V → V → ℝ} {A : ℝ}

/-- **The third iterate of the bounded operator acts by the cube kernel.**  Operator-level form
of `kernelApply_three_eq_of_schurKernel`: on real `ℓ²`, `T_κ³ = T_{κ³}`, with
`SchurKernel (kernelComp κ κ) (A * A)` no longer assumed. -/
theorem kernelCLM_cube_apply (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) (x : V) :
    (kernelCLM h (kernelCLM h (kernelCLM h f)) : V → ℝ) x
      = ∑' z, kernelCube κ x z * (f : V → ℝ) z :=
  kernelApply_three_eq_of_schurKernel h (summable_sq_of_memℓp f) x

/-- **The cube of the bounded operator is the bounded operator of the cube kernel.** -/
theorem kernelCLM_three_apply_eq (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) (x : V) :
    (kernelCLM h (kernelCLM h (kernelCLM h f)) : V → ℝ) x
      = (kernelCLM (schurKernel_kernelCube h) f : V → ℝ) x := by
  rw [kernelCLM_cube_apply h f x, kernelCLM_apply_eq_tsum]

/-- **The square of the bounded operator is the bounded operator of the two-fold kernel**:
`T_κ.comp T_κ = T_{κ * κ}` as bounded operators on real `ℓ²`. -/
theorem kernelCLM_comp_self_eq (h : SchurKernel κ A) :
    (kernelCLM h).comp (kernelCLM h) = kernelCLM (schurKernel_kernelComp h) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.comp_apply]
  refine lp.ext ?_
  funext x
  rw [kernelCLM_comp_apply h f x, kernelCLM_apply_eq_tsum]

/-- **The cube of the bounded operator is the bounded operator of the cube kernel**:
`T_κ.comp (T_κ.comp T_κ) = T_{κ³}` as bounded operators on real `ℓ²`, with no hypothesis on the
two-fold kernel. -/
theorem kernelCLM_comp_three_eq (h : SchurKernel κ A) :
    (kernelCLM h).comp ((kernelCLM h).comp (kernelCLM h)) =
      kernelCLM (schurKernel_kernelCube h) := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  refine lp.ext ?_
  funext x
  rw [kernelCLM_cube_apply h f x, kernelCLM_apply_eq_tsum]

/-- **The cube operator has operator norm at most `A³`.** -/
theorem kernelCLM_cube_norm_le (h : SchurKernel κ A) :
    ‖kernelCLM (schurKernel_kernelCube h)‖ ≤ A * (A * A) :=
  kernelCLM_norm_le (schurKernel_kernelCube h)

/-- **The packaged operator is self-adjoint**, and its quadratic form is the column-sum
formula `⟪T f, f⟫ = ∑_y f y · ∑_x κ x y f x`. -/
theorem kernelCLM_quadratic_form (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    inner ℝ (kernelCLM h f) f
        = ∑' y, (f : V → ℝ) y * ∑' x, κ x y * (f : V → ℝ) x ∧
      ContinuousLinearMap.adjoint (kernelCLM h) = kernelCLM h :=
  ⟨inner_kernelCLM_eq h f f, kernelCLM_adjoint_eq h⟩

/-- **Summary of the discharge.**  A single Schur hypothesis `SchurKernel κ A` gives: the
composed kernel and the cube kernel are Schur kernels with constants `A * A` and `A * (A * A)`;
the kernel operator is a bounded linear map on real `ℓ²` of norm at most `A` with the kernel
formula; its square acts by `kernelComp κ κ`; and its cube acts by `kernelCube κ`. -/
theorem schur_summary (h : SchurKernel κ A) :
    SchurKernel (kernelComp κ κ) (A * A) ∧
      SchurKernel (kernelCube κ) (A * (A * A)) ∧
      ∃ T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2,
        ‖T‖ ≤ A ∧
          (∀ (f : lp (fun _ : V => ℝ) 2) (x : V),
            (T f : V → ℝ) x = ∑' y, κ x y * (f : V → ℝ) y) ∧
          (∀ (f : lp (fun _ : V => ℝ) 2) (x : V),
            (T (T f) : V → ℝ) x = ∑' z, kernelComp κ κ x z * (f : V → ℝ) z) ∧
          (∀ (f : lp (fun _ : V => ℝ) 2) (x : V),
            (T (T (T f)) : V → ℝ) x = ∑' z, kernelCube κ x z * (f : V → ℝ) z) ∧
          ContinuousLinearMap.adjoint T = T :=
  ⟨schurKernel_kernelComp h, schurKernel_kernelCube h,
    kernelCLM h, kernelCLM_norm_le h, kernelCLM_apply_eq_tsum h, kernelCLM_comp_apply h,
    kernelCLM_cube_apply h, kernelCLM_adjoint_eq h⟩

end PercLib.CriticalLRP.KernelOperator
