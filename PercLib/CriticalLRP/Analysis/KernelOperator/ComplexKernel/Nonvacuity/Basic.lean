/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

A compiled non-vacuity witness for the complex kernel operator package.

Swarm `smwtxo95t`, member `m1`, direction (D) "concrete complex kernel operator".

The hypotheses of `exists_sqrt_cube_kernelCLM` (a `SchurKernel`, and positivity of the real
quadratic form) are met by the constant-one kernel on the one-point lattice, whose operator is
the identity.  So the CFC square-root statement is not vacuous, and the operator is not forced
to vanish.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.CFC
public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.Nonvacuity.Defs

/-!
# A non-vacuous instance: the constant-one kernel on `Unit`
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp InnerProduct InnerProductSpace

namespace PercLib.CriticalLRP.KernelOperator

/-- **The constant-one kernel is a Schur kernel with constant `1`.** -/
theorem schurKernel_oneKernel : SchurKernel oneKernel 1 where
  nonneg := fun _ _ => zero_le_one
  symm := fun _ _ => rfl
  nonneg_A := zero_le_one
  row_summable := fun _ => Summable.of_finite
  row_le := fun _ => by simp [oneKernel]

/-- The real kernel operator of the constant-one kernel is the identity on the one-point
lattice. -/
theorem kernelCLM_oneKernel_apply (a : lp (fun _ : Unit => ℝ) 2) (x : Unit) :
    (kernelCLM schurKernel_oneKernel a : Unit → ℝ) x = (a : Unit → ℝ) x := by
  have hx : x = () := Subsingleton.elim x ()
  subst hx
  rw [kernelCLM_apply_eq_tsum]
  simp [oneKernel]

theorem kernelCLM_oneKernel_eq_self (a : lp (fun _ : Unit => ℝ) 2) :
    kernelCLM schurKernel_oneKernel a = a := by
  refine lp.ext ?_
  funext x
  exact kernelCLM_oneKernel_apply a x

/-- **The real quadratic form of the one-point kernel operator is nonnegative.** -/
theorem inner_oneKernel_nonneg (a : lp (fun _ : Unit => ℝ) 2) :
    0 ≤ ⟪kernelCLM schurKernel_oneKernel a, a⟫_ℝ := by
  rw [kernelCLM_oneKernel_eq_self, lp.inner_eq_tsum]
  exact tsum_nonneg fun x => by
    rw [real_inner_eq_mul]
    exact mul_self_nonneg _

/-- The complex operator of the constant-one kernel is not the zero operator. -/
theorem kernelCLMℂ_oneKernel_apply_one :
    (kernelCLMℂ schurKernel_oneKernel (Realification.ofRealLp oneLp) : Unit → ℂ) () = 1 := by
  rw [kernelCLMℂ_apply_eq_tsum]
  simp [oneKernel, Realification.ofRealLp, oneLp]

theorem kernelCLMℂ_oneKernel_ne_zero :
    kernelCLMℂ schurKernel_oneKernel (Realification.ofRealLp oneLp) ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : lp (fun _ : Unit => ℂ) 2 => (f : Unit → ℂ) ()) h
  rw [kernelCLMℂ_oneKernel_apply_one] at h1
  simp at h1

/-- **Non-vacuity of the CFC square-root statement**: the constant-one kernel on the one-point
lattice satisfies all hypotheses of `exists_sqrt_cube_kernelCLM`, and the resulting operator is
the square root of the cube of a nonzero operator. -/
theorem exists_sqrt_cube_oneKernel :
    ∃ S : lp (fun _ : Unit => ℂ) 2 →L[ℂ] lp (fun _ : Unit => ℂ) 2,
      0 ≤ S ∧ S† = S ∧
        S† * S = kernelCLMℂ (schurKernel_kernelCube schurKernel_oneKernel) ∧
        (∀ a : lp (fun _ : Unit => ℝ) 2,
          ⟪((kernelCLM schurKernel_oneKernel) ^ 3) a, a⟫_ℝ
            = RCLike.re ⟪S (Realification.ofRealLp a), S (Realification.ofRealLp a)⟫_ℂ) :=
  exists_sqrt_cube_kernelCLM schurKernel_oneKernel inner_oneKernel_nonneg

end PercLib.CriticalLRP.KernelOperator

set_option linter.hashCommand false

/-! ### Axiom audit -/
#print axioms PercLib.CriticalLRP.KernelOperator.schurKernel_oneKernel
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLM_oneKernel_apply
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLM_oneKernel_eq_self
#print axioms PercLib.CriticalLRP.KernelOperator.inner_oneKernel_nonneg
#print axioms PercLib.CriticalLRP.KernelOperator.oneLp
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ_oneKernel_apply_one
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ_oneKernel_ne_zero
#print axioms PercLib.CriticalLRP.KernelOperator.exists_sqrt_cube_oneKernel
