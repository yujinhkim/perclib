/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The Gaussian/Laplace regime of Definition I.5.16, instantiated with Mathlib's Gaussian measures:
for a centred Gaussian probability measure `γ` on `E` with covariance bilinear form `covarianceBilin γ`,
the law of `B_T` (`B` Brownian with that covariance, `T ~ Exp(1)` independent) exists as an honest
probability measure with characteristic function `u ↦ (1 + covarianceBilin γ u u / 2)⁻¹`.
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.Dispersion
public import Mathlib.Probability.Distributions.Gaussian.CharFun

set_option autoImplicit true

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise

namespace PercLib.CriticalLRP.LevyAnalysis

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The Riesz vector of a continuous bilinear form: `⟪rieszOp B u, v⟫ = B u v`. -/
noncomputable def rieszOp (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E where
  toLinearMap := ((InnerProductSpace.toDual ℝ E).symm.toLinearEquiv).toLinearMap.comp B.toLinearMap
  cont := LinearMap.continuous_of_finiteDimensional _

theorem toDual_rieszOp (B : E →L[ℝ] E →L[ℝ] ℝ) (u : E) :
    InnerProductSpace.toDual ℝ E (rieszOp B u) = B u := by
  simp [rieszOp]

theorem rieszOp_inner (B : E →L[ℝ] E →L[ℝ] ℝ) (u : E) :
    inner ℝ (rieszOp B u) u = B u u := by
  have h2 := InnerProductSpace.toDual_apply_apply (𝕜 := ℝ) (x := rieszOp B u) (y := u)
  rw [toDual_rieszOp] at h2
  exact h2.symm

/-- **Definition I.5.16, `α ≥ 2`, for Mathlib's Gaussian measures.** -/
theorem exists_laplaceMixture_isGaussian (γ : Measure E) [IsProbabilityMeasure γ] [IsGaussian γ]
    (hmean : ∫ x, id x ∂γ = 0) :
    ∃ ν : ProbabilityMeasure E, ∀ u : E,
      charFun (ν : Measure E) u = (1 + ((covarianceBilin γ u u : ℝ) : ℂ) / 2)⁻¹ := by
  have hpos : ∀ u : E, 0 ≤ (inner ℝ (rieszOp (covarianceBilin γ) u) u : ℝ) := by
    intro u
    rw [rieszOp_inner]
    exact covarianceBilin_self_nonneg u
  obtain ⟨ν, hν⟩ := exists_laplaceMixture γ (rieszOp (covarianceBilin γ)) hpos (fun u => by
    rw [rieszOp_inner, IsGaussian.charFun_eq', hmean]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    rw [neg_div])
  exact ⟨ν, fun u => by rw [hν u, rieszOp_inner]⟩
