/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The CFC square root of the cube of the complex Schur kernel operator.

Swarm `smwtxo95t`, member `m1`, direction (D) "concrete complex kernel operator".

`Analysis/KernelOperator/CFC.lean` proves, conditionally on a complex-linear extension `Tℂ` of a
real operator `T` and on positivity of the real quadratic form, the existence of a nonnegative
self-adjoint `S` with `S† * S = Tℂ^3` and the Gram identity
`⟪T^3 a, a⟫ = re ⟪S a, S a⟫`.  `Basic.lean`/`SelfAdjoint.lean` supply both hypotheses for the
Schur kernel operator `T = kernelCLM h`: the extension is `kernelCLMℂ h`, it is self-adjoint by
symmetry of `κ`, and `Tℂ^3` is the operator of the cube kernel `kernelCube κ` (the model's
`openTriangle`).  Positivity of the real quadratic form is kept as an explicit hypothesis:
nothing here derives it from the Schur bound.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.SelfAdjoint

/-!
# The `3/2`-power of the complex kernel operator

The cube of `kernelCLMℂ h` is the operator of `kernelCube κ`, so its CFC square root is a square
root of the `openTriangle` operator — conditionally on positivity of the real quadratic form.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp InnerProduct InnerProductSpace

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*} {κ : V → V → ℝ} {A : ℝ}

/-- **The cubic form of the kernel operator is the cubic form of the cube kernel.**  This is the
form in which the campaign's `openTriangle` enters: `⟪T^3 a, a⟫` is the finite quadratic form of
`kernelCube κ` against `a`. -/
theorem inner_pow_three_eq_tsum_kernelCube (h : SchurKernel κ A)
    (a : lp (fun _ : V => ℝ) 2) :
    ⟪((kernelCLM h) ^ 3) a, a⟫_ℝ
      = ∑' x, (a : V → ℝ) x * ∑' z, kernelCube κ x z * (a : V → ℝ) z := by
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun x => ?_
  rw [real_inner_eq_mul, kernelCLM_pow_three_apply, kernelApply]

/-- **The CFC square root of the cube of the complex kernel operator.**  For a Schur kernel
`κ` whose real quadratic form is nonnegative, `(kernelCLMℂ h)^(3/2) = CFC.sqrt ((kernelCLMℂ h)^3)`
is a nonnegative self-adjoint operator whose square is the `openTriangle` operator, and the real
cubic form of the kernel operator is its Gram form on real-valued vectors. -/
theorem exists_sqrt_cube_kernelCLM (h : SchurKernel κ A)
    (hpos : ∀ a : lp (fun _ : V => ℝ) 2, 0 ≤ ⟪kernelCLM h a, a⟫_ℝ) :
    ∃ S : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2,
      0 ≤ S ∧ S† = S ∧ S† * S = kernelCLMℂ (schurKernel_kernelCube h) ∧
        (∀ a, ⟪((kernelCLM h) ^ 3) a, a⟫_ℝ
          = RCLike.re ⟪S (Realification.ofRealLp a), S (Realification.ofRealLp a)⟫_ℂ) := by
  obtain ⟨S, hS0, hSadj, hSsq, hGram⟩ :=
    Realification.exists_sqrt_cube_real_operator (kernelCLM h) (kernelCLMℂ h)
      (kernelCLMℂ_ofRealLp h) (isSelfAdjoint_kernelCLMℂ h) hpos
  exact ⟨S, hS0, hSadj, by rw [hSsq, kernelCLMℂ_pow_three_eq], hGram⟩

/-- **The Gram form of the square root is the cubic form of the cube kernel.**  Direct
combination of `exists_sqrt_cube_kernelCLM` with `inner_pow_three_eq_tsum_kernelCube`, so the
CFC output is tied to the `openTriangle` series without any further identification. -/
theorem exists_sqrt_cube_kernelCLM_gram (h : SchurKernel κ A)
    (hpos : ∀ a : lp (fun _ : V => ℝ) 2, 0 ≤ ⟪kernelCLM h a, a⟫_ℝ) :
    ∃ S : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2,
      0 ≤ S ∧ S† = S ∧ S† * S = kernelCLMℂ (schurKernel_kernelCube h) ∧
        (∀ a : lp (fun _ : V => ℝ) 2,
          ∑' x, (a : V → ℝ) x * ∑' z, kernelCube κ x z * (a : V → ℝ) z
          = RCLike.re ⟪S (Realification.ofRealLp a), S (Realification.ofRealLp a)⟫_ℂ) := by
  obtain ⟨S, hS0, hSadj, hSsq, hGram⟩ := exists_sqrt_cube_kernelCLM h hpos
  exact ⟨S, hS0, hSadj, hSsq, fun (a : lp (fun _ : V => ℝ) 2) => by
    rw [← inner_pow_three_eq_tsum_kernelCube h a, hGram a]⟩

end PercLib.CriticalLRP.KernelOperator

set_option linter.hashCommand false

/-! ### Axiom audit -/
#print axioms PercLib.CriticalLRP.KernelOperator.inner_pow_three_eq_tsum_kernelCube
#print axioms PercLib.CriticalLRP.KernelOperator.exists_sqrt_cube_kernelCLM
#print axioms PercLib.CriticalLRP.KernelOperator.exists_sqrt_cube_kernelCLM_gram
