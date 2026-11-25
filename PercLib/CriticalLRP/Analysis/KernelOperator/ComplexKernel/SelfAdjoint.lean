/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The complex Schur kernel operator: self-adjointness, uniqueness of the complex extension,
and compatibility of composition and powers.

Swarm `smwtxo95t`, member `m1`, direction (D) "concrete complex kernel operator".

The real operator `kernelCLM h` is self-adjoint (`InnerProduct.lean`,
`inner_kernelCLM_comm`).  The realification bridge of `CFC.lean` turns that symmetry into
self-adjointness of any complex-linear extension on `lp (V, ℂ) 2`, and the same uniqueness
lemma (`ext_of_eqOn_real`) identifies the square and the cube of `kernelCLMℂ h` with the
operators of `kernelComp κ κ` and `kernelCube κ`.  In particular `(kernelCLMℂ h)^3` *is* the
threefold composed Schur-kernel operator, so the CFC square root of `Tℂ^3` produced in
`CFC.lean` is the square root of the `openTriangle` operator.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.Basic
public import PercLib.CriticalLRP.Analysis.KernelOperator.InnerProduct
public import PercLib.CriticalLRP.Analysis.KernelOperator.CFC
public import PercLib.CriticalLRP.Analysis.KernelOperator.SchurComp

/-!
# Self-adjointness and powers of the complex kernel operator

No positivity is assumed in this file: symmetry of `κ` is what makes `kernelCLMℂ h`
self-adjoint, and the power identities are operator identities.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp InnerProduct InnerProductSpace

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*} {κ : V → V → ℝ} {A : ℝ}

/-! ### Self-adjointness -/

/-- **The complex kernel operator is self-adjoint.**  Derived from symmetry of the real
operator through the realification bridge: the imaginary cross-terms of the quadratic form
cancel by symmetry. -/
theorem isSelfAdjoint_kernelCLMℂ (h : SchurKernel κ A) : IsSelfAdjoint (kernelCLMℂ h) :=
  Realification.isSelfAdjoint_complexification_of_symmetric Realification.ofRealLp
    Realification.inner_ofRealLp Realification.exists_ofRealLp_add (kernelCLM h) (kernelCLMℂ h)
    (kernelCLMℂ_ofRealLp h) (fun a b => inner_kernelCLM_comm h a b)

/-- **The adjoint of the complex kernel operator is itself.** -/
theorem kernelCLMℂ_adjoint (h : SchurKernel κ A) :
    ContinuousLinearMap.adjoint (kernelCLMℂ h) = kernelCLMℂ h := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using (isSelfAdjoint_kernelCLMℂ h).star_eq

/-- **The complex bilinear form is symmetric.** -/
theorem inner_kernelCLMℂ_comm (h : SchurKernel κ A) (f g : lp (fun _ : V => ℂ) 2) :
    ⟪kernelCLMℂ h f, g⟫_ℂ = ⟪f, kernelCLMℂ h g⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_left (kernelCLMℂ h) g f, kernelCLMℂ_adjoint h]

/-! ### Uniqueness of the complex extension -/

/-- **Any complex-linear operator that agrees with the real kernel operator on real-valued
`ℓ²` functions is `kernelCLMℂ h`.**  So the construction above is not an extra choice: it is
the unique complex-linear extension of the real Schur operator. -/
theorem eq_kernelCLMℂ_of_agrees_on_real (h : SchurKernel κ A)
    {S : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2}
    (hS : ∀ a, S (Realification.ofRealLp a) = Realification.ofRealLp (kernelCLM h a)) :
    S = kernelCLMℂ h := by
  refine Realification.ext_of_eqOn_real Realification.ofRealLp
    Realification.exists_ofRealLp_add ?_
  intro a
  rw [hS a, kernelCLMℂ_ofRealLp h]

/-! ### Composition and powers -/

/-- **The square of the complex operator is the operator of the composed kernel.** -/
theorem kernelCLMℂ_mul_self (h : SchurKernel κ A) :
    kernelCLMℂ h * kernelCLMℂ h = kernelCLMℂ (schurKernel_kernelComp h) := by
  refine Realification.ext_of_eqOn_real Realification.ofRealLp
    Realification.exists_ofRealLp_add ?_
  intro a
  rw [mul_apply_eq_comp, kernelCLMℂ_ofRealLp h, kernelCLMℂ_ofRealLp h,
    kernelCLMℂ_ofRealLp (schurKernel_kernelComp h)]
  congr 1
  refine lp.ext ?_
  funext x
  rw [kernelCLM_comp_apply h a x, kernelCLM_apply_eq_tsum]

/-- **Powers of the complex operator extend powers of the real one.** -/
theorem kernelCLMℂ_pow_ofRealLp (h : SchurKernel κ A) (n : ℕ)
    (a : lp (fun _ : V => ℝ) 2) :
    ((kernelCLMℂ h) ^ n) (Realification.ofRealLp a)
      = Realification.ofRealLp (((kernelCLM h) ^ n) a) :=
  Realification.complexification_pow_apply Realification.ofRealLp (kernelCLM h) (kernelCLMℂ h)
    (kernelCLMℂ_ofRealLp h) n a

/-- **The real third iterate acts by the cube kernel.** -/
theorem kernelCLM_pow_three_apply (h : SchurKernel κ A) (a : lp (fun _ : V => ℝ) 2) (x : V) :
    (((kernelCLM h) ^ 3) a : V → ℝ) x = kernelApply (kernelCube κ) (a : V → ℝ) x := by
  have h1 : ((kernelCLM h) ^ 3) a = kernelCLM h (kernelCLM h (kernelCLM h a)) := by
    rw [pow_three]
    rfl
  rw [h1]
  exact (kernelApply_cube_eq h (summable_sq_of_memℓp a) x).symm

/-- **The complex third iterate acts by the cube kernel**, i.e. by `openTriangle`. -/
theorem kernelCLMℂ_pow_three_apply (h : SchurKernel κ A) (a : lp (fun _ : V => ℝ) 2)
    (x : V) :
    (((kernelCLMℂ h) ^ 3) (Realification.ofRealLp a) : V → ℂ) x
      = ∑' z, (kernelCube κ x z : ℂ) * ((a : V → ℝ) z) := by
  rw [kernelCLMℂ_pow_ofRealLp h 3 a]
  change (((((kernelCLM h) ^ 3) a : V → ℝ) x : ℝ) : ℂ)
    = ∑' z, (kernelCube κ x z : ℂ) * ((a : V → ℝ) z)
  rw [kernelCLM_pow_three_apply h a x, kernelApply, Complex.ofReal_tsum]
  exact tsum_congr fun z => by push_cast; ring

/-- **The cube of the complex operator is the operator of the cube kernel.** -/
theorem kernelCLMℂ_pow_three_eq (h : SchurKernel κ A) :
    (kernelCLMℂ h) ^ 3 = kernelCLMℂ (schurKernel_kernelCube h) := by
  refine Realification.ext_of_eqOn_real Realification.ofRealLp
    Realification.exists_ofRealLp_add ?_
  intro a
  rw [kernelCLMℂ_pow_ofRealLp h 3 a, kernelCLMℂ_ofRealLp (schurKernel_kernelCube h)]
  congr 1
  refine lp.ext ?_
  funext x
  rw [kernelCLM_pow_three_apply h a x]
  rfl

end PercLib.CriticalLRP.KernelOperator

set_option linter.hashCommand false

/-! ### Axiom audit -/
#print axioms PercLib.CriticalLRP.KernelOperator.isSelfAdjoint_kernelCLMℂ
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ_adjoint
#print axioms PercLib.CriticalLRP.KernelOperator.inner_kernelCLMℂ_comm
#print axioms PercLib.CriticalLRP.KernelOperator.eq_kernelCLMℂ_of_agrees_on_real
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ_mul_self
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ_pow_ofRealLp
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLM_pow_three_apply
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ_pow_three_apply
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ_pow_three_eq
