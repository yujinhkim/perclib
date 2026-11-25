/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.LevyAnalysis.Radial

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Metric Set Filter ContinuousLinearMap
open Module
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.LevyAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The ball-integrated bilinear form associated with a continuous bilinear map. -/
noncomputable def ballBilinearIntegral (μ : Measure E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) : ℝ :=
  ∫ y in ball (0 : E) 1, (B y u) * (B y v) ∂μ

/-- The associated positive quadratic ball integral. -/
noncomputable def ballQuadraticIntegral (μ : Measure E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (u : E) : ℝ :=
  ∫ y in ball (0 : E) 1, (B y u) ^ 2 ∂μ

variable {μ : Measure E} [μ.IsAddHaarMeasure]
variable {B : E →L[ℝ] E →L[ℝ] ℝ}

theorem integrable_ball_quadratic (u v : E) :
    IntegrableOn (fun y : E => (B y u) * (B y v)) (ball (0 : E) 1) μ := by
  have hu' : Continuous fun y : E => B y u := (B.flip u).continuous
  have hv' : Continuous fun y : E => B y v := (B.flip v).continuous
  have hc : Continuous fun y : E => (B y u) * (B y v) := hu'.mul hv'
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) 1)).mono_set
    ball_subset_closedBall

set_option linter.unusedSectionVars false in
theorem ballBilinearIntegral_nonneg (u : E) : 0 ≤ ballBilinearIntegral μ B u u := by
  dsimp [ballBilinearIntegral]
  apply integral_nonneg
  intro y
  exact mul_self_nonneg _

theorem ballBilinearIntegral_pos_of_diag_ne_zero {u : E} (hu : B u u ≠ 0) :
    0 < ballBilinearIntegral μ B u u := by
  let c : ℝ := (2 * (‖u‖ + 1))⁻¹
  let x : E := c • u
  have hc : 0 < c := by dsimp [c]; positivity
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hund : ‖u‖ < 2 * (‖u‖ + 1) := by nlinarith [norm_nonneg u]
  have hxnorm : ‖x‖ < 1 := by
    calc ‖x‖ = c * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      _ < 1 := by
        rw [show c * ‖u‖ = ‖u‖ / (2 * (‖u‖ + 1)) by
          dsimp [c]; rw [div_eq_mul_inv, mul_comm]]
        exact (div_lt_one (by positivity)).2 hund
  have hx : x ∈ ball (0 : E) 1 := by simpa [mem_ball, dist_zero_right] using hxnorm
  have hBx : B x u ≠ 0 := by
    rw [show B x u = c * B u u by dsimp [x]; rw [map_smul]; exact rfl]
    exact mul_ne_zero hc0 hu
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun y : E => mul_self_nonneg (B y u))
    (by simpa [pow_two] using integrable_ball_quadratic (μ := μ) (B := B) u u)).2
  have hucont : Continuous fun y : E => B y u := (B.flip u).continuous
  have hprodcont : Continuous fun y : E => B y u * B y u := hucont.mul hucont
  have hopen : IsOpen {y : E | 0 < B y u * B y u} :=
    isOpen_lt continuous_const hprodcont
  have hpos := (hopen.inter isOpen_ball).measure_pos μ
    (show ({y : E | 0 < B y u * B y u} ∩ ball (0 : E) 1).Nonempty from
      ⟨x, mul_self_pos.mpr hBx, hx⟩)
  apply lt_of_lt_of_le hpos (measure_mono ?_)
  intro y hy
  refine ⟨show B y u * B y u ≠ 0 by
    intro hzero
    exact hy.1.ne' hzero, hy.2⟩

set_option linter.unusedSectionVars false in
theorem ballQuadraticIntegral_eq_self (u : E) :
    ballQuadraticIntegral μ B u = ballBilinearIntegral μ B u u := by
  unfold ballQuadraticIntegral ballBilinearIntegral
  congr 1
  funext y
  ring

theorem ballQuadraticIntegral_pos_of_diag_ne_zero {u : E} (hu : B u u ≠ 0) :
    0 < ballQuadraticIntegral μ B u := by
  rw [ballQuadraticIntegral_eq_self]
  exact ballBilinearIntegral_pos_of_diag_ne_zero hu

/-- Radial scaling of a homogeneous quadratic Bochner integral over balls. -/
theorem integral_ball_quadratic_hom (u : E) {r : ℝ} (hr : 0 < r) :
    ∫ y in ball (0 : E) r, (B y u) ^ 2 ∂μ =
      r ^ (2 + (Module.finrank ℝ E : ℝ)) * ∫ y in ball (0 : E) 1, (B y u) ^ 2 ∂μ := by
  let P : E → ℝ := fun y => (B y u) ^ 2
  have hP : ∀ x, 0 ≤ P x := fun x => sq_nonneg _
  have hPm : Measurable P := by
    exact ((B.flip u).continuous.pow 2).measurable
  have hhom : ∀ (c : ℝ), 0 < c → ∀ x, P (c • x) = c ^ (2 : ℝ) * P x := by
    intro c hc x
    dsimp [P]
    rw [map_smul, smul_apply]
    simp only [smul_eq_mul]
    norm_cast
    ring
  have hlin := lintegral_ball_hom μ hP hPm hhom hr
  have hintR : IntegrableOn P (ball (0 : E) r) μ := by
    have hc : Continuous fun y : E => (B y u) ^ 2 := ((B.flip u).continuous).pow 2
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) r)).mono_set
      ball_subset_closedBall
  have hint1 : IntegrableOn P (ball (0 : E) 1) μ := by
    simpa [P, pow_two] using integrable_ball_quadratic (μ := μ) (B := B) u u
  have hnn : ∀ᵐ y ∂(μ.restrict (ball (0:E) r)), 0 ≤ P y := by
    exact Eventually.of_forall hP
  have hnn1 : ∀ᵐ y ∂(μ.restrict (ball (0:E) 1)), 0 ≤ P y := by
    exact Eventually.of_forall hP
  rw [← ofReal_integral_eq_lintegral_ofReal hintR hnn,
    ← ofReal_integral_eq_lintegral_ofReal hint1 hnn1] at hlin
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le (2 + (Module.finrank ℝ E : ℝ)))] at hlin
  have hleft : 0 ≤ ∫ y in ball (0 : E) r, P y ∂μ := integral_nonneg (fun y => hP y)
  have hright : 0 ≤ r ^ (2 + (Module.finrank ℝ E : ℝ)) * ∫ y in ball (0 : E) 1, P y ∂μ := by
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (integral_nonneg (fun y => hP y))
  have heq := (ENNReal.ofReal_eq_ofReal_iff hleft hright).mp hlin
  simpa [P] using heq

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The paper's `∫_B ⟨y, u⟩² dy` as a real Bochner integral on the unit ball. -/
noncomputable def ballInnerMoment (u : E) : ℝ :=
  ∫ y in ball (0 : E) 1, (inner ℝ y u) ^ 2 ∂μ

theorem ballInnerMoment_eq_quadratic (u : E) :
    ballInnerMoment μ u = ballQuadraticIntegral μ ((innerSL ℝ (E := E))) u := by
  unfold ballInnerMoment ballQuadraticIntegral
  rfl

theorem ballInnerMoment_pos {u : E} (hu : u ≠ 0) : 0 < ballInnerMoment μ u := by
  rw [ballInnerMoment_eq_quadratic]
  apply ballQuadraticIntegral_pos_of_diag_ne_zero
  rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  exact pow_ne_zero 2 (norm_pos_iff.mpr hu).ne'

theorem integral_ball_innerMoment_scaling {u : E} {r : ℝ} (hr : 0 < r) :
    ∫ y in ball (0 : E) r, (inner ℝ y u) ^ 2 ∂μ =
      r ^ (2 + (Module.finrank ℝ E : ℝ)) * ballInnerMoment μ u := by
  rw [ballInnerMoment_eq_quadratic]
  exact integral_ball_quadratic_hom (μ := μ) (B := (innerSL ℝ (E := E))) u hr

#print axioms PercLib.CriticalLRP.LevyAnalysis.ballQuadraticIntegral_pos_of_diag_ne_zero
#print axioms PercLib.CriticalLRP.LevyAnalysis.ballInnerMoment_pos
#print axioms PercLib.CriticalLRP.LevyAnalysis.integral_ball_innerMoment_scaling

end InnerProduct


end PercLib.CriticalLRP.LevyAnalysis
