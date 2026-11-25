/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I:
High effective dimension", arXiv:2508.18807v1, Section I.5.2.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

/-!
# Radial (homogeneous) integration on a finite-dimensional real normed space

This file develops the elementary "polar-coordinates-free" radial integration
lemmas used to compute the moments of the Lévy measures `Π₁`, `Π_λ`, `Π_∞` of
Section I.5.2 of the paper, and the moment bounds for the Riesz/Green kernels.

The ambient setting is deliberately general, matching Definition I.1.3: `E` is a
finite-dimensional real normed space (the paper allows an arbitrary norm
`‖·‖`), `μ` is an additive Haar measure (Lebesgue measure), and the paper's
normalization (∗) `|B₁| = 1` is *not* used in the identities below: the unit
ball mass `μ (ball 0 1)` appears as an explicit constant.

Main results:

* `CLRP.lintegral_ball_hom`: for `P` nonnegative, measurable, homogeneous of
  degree `k`, `∫⁻ x in ball 0 r, P x = r ^ (k + d) * ∫⁻ x in ball 0 1, P x`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open Module
open scoped ENNReal NNReal Topology Pointwise

namespace PercLib.CriticalLRP.LevyAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Change of variables `x ↦ c⁻¹ • x` for a nonnegative `c`, for Lebesgue
integrals of nonnegative functions. -/
theorem lintegral_inv_smul (μ : Measure E) [μ.IsAddHaarMeasure] (c : ℝ) (hc : 0 < c)
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x, g (c⁻¹ • x) ∂μ = ENNReal.ofReal (c ^ (finrank ℝ E : ℕ)) * ∫⁻ x, g x ∂μ := by
  rw [← lintegral_map (f := g) (g := fun x : E => c⁻¹ • x) hg (measurable_const_smul _)]
  rw [Measure.map_addHaar_smul μ (inv_ne_zero hc.ne'), lintegral_smul_measure]
  congr 1
  rw [abs_of_nonneg (by positivity), inv_pow, inv_inv]

/-- The change of variables `x = c • y` on a ball: the ball of radius `c` maps to the
unit ball. -/
theorem lintegral_ball_comp_smul (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → ℝ≥0∞)
    (hF : Measurable F) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x in ball (0 : E) c, F x ∂μ
      = ENNReal.ofReal (c ^ (finrank ℝ E : ℕ)) * ∫⁻ y in ball (0 : E) 1, F (c • y) ∂μ := by
  set g : E → ℝ≥0∞ := (ball (0 : E) 1).indicator (fun y => F (c • y)) with hg_def
  have hg : Measurable g := (hF.comp (measurable_const_smul c)).indicator measurableSet_ball
  have hmem : ∀ x : E, c⁻¹ • x ∈ ball (0 : E) 1 ↔ x ∈ ball (0 : E) c := by
    intro x
    simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hc, inv_mul_lt_iff₀ hc, mul_one]
  have key : ∫⁻ x in ball (0 : E) c, F x ∂μ = ∫⁻ x, g (c⁻¹ • x) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball (f := F)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ ball (0 : E) c
    · rw [indicator_of_mem hx, hg_def]
      simp only [indicator_of_mem (hmem x |>.2 hx), smul_inv_smul₀ hc.ne' x]
    · rw [indicator_of_notMem hx, hg_def]
      simp only [indicator_of_notMem (fun h => hx (hmem x |>.1 h))]
  rw [key, lintegral_inv_smul μ c hc g hg, hg_def, lintegral_indicator measurableSet_ball]

/-- Radial scaling of the integral of a homogeneous function over a ball. -/
theorem lintegral_ball_hom (μ : Measure E) [μ.IsAddHaarMeasure] {P : E → ℝ}
    (hP : ∀ x, 0 ≤ P x) (hPm : Measurable P) {k : ℝ}
    (hhom : ∀ (c : ℝ), 0 < c → ∀ x, P (c • x) = c ^ k * P x)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (P x) ∂μ
      = ENNReal.ofReal (r ^ (k + (finrank ℝ E : ℝ)))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ := by
  have hPt : ∀ y, ENNReal.ofReal (P (r • y)) = ENNReal.ofReal (r ^ k) * ENNReal.ofReal (P y) := by
    intro y
    rw [hhom r hr y, ENNReal.ofReal_mul (Real.rpow_nonneg hr.le k)]
  have hinner : ∫⁻ y in ball (0 : E) 1, ENNReal.ofReal (P (r • y)) ∂μ
      = ENNReal.ofReal (r ^ k) * ∫⁻ y in ball (0 : E) 1, ENNReal.ofReal (P y) ∂μ := by
    rw [lintegral_congr hPt]
    exact lintegral_const_mul'' _ hPm.ennreal_ofReal.aemeasurable
  rw [lintegral_ball_comp_smul μ _ hPm.ennreal_ofReal hr, hinner, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_natCast, ← Real.rpow_add hr, add_comm]

end PercLib.CriticalLRP.LevyAnalysis
