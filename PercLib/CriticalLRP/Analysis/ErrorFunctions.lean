module

public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.LogError

set_option autoImplicit false

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

/-- Negation preserves the logarithmically integrable error property. -/
theorem isLogErrorFunction_neg {h : ℝ → ℝ} (hh : IsLogErrorFunction h) :
    IsLogErrorFunction (fun r => -h r) := by
  obtain ⟨⟨hmeas, r₀, hr₀, hint⟩, h0⟩ := hh
  refine ⟨⟨hmeas.neg, r₀, hr₀, ?_⟩, ?_⟩
  · simpa only [abs_neg] using hint
  · simpa using h0.neg

/-- An eventually `O(1/r)` term with a measurable representative is a
logarithmically integrable error function. -/
theorem isLogErrorFunction_of_denominator_bound {q : ℝ → ℝ} (hq : Measurable q)
    {c r₀ : ℝ} (hc : 0 ≤ c) (hr₀ : 0 < r₀)
    (hbound : ∀ r, r₀ ≤ r → |q r| ≤ c * r⁻¹) :
    IsLogErrorFunction q := by
  have hb_main : ∀ r, r₀ ≤ r → |q r| ≤ c * r ^ (-1 : ℝ) := by
    intro r hr
    rw [show r ^ (-1 : ℝ) = r⁻¹ by rw [Real.rpow_neg_one]]
    exact hbound r hr
  have hc_err := isLogErrorFunction_const_rpow_neg (a := 1) (c := c) (r₀ := r₀) one_pos hr₀
  obtain ⟨_, hc0⟩ := hc_err
  have hint_c : IntegrableOn (fun r => c * r ^ (-2 : ℝ)) (Ioi r₀) volume :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hr₀).const_mul c
  have hint : IntegrableOn (fun r => |q r| / r) (Ioi r₀) volume := by
    refine hint_c.mono' (μ := volume.restrict (Ioi r₀))
      (hq.abs.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrpos : 0 < r := hr₀.trans hr
    have hnonneg : 0 ≤ c * r ^ (-1 : ℝ) := by positivity
    rw [show c * r ^ (-2 : ℝ) = |c * r ^ (-1 : ℝ)| / r by
      rw [show (-2 : ℝ) = -1 + (-1) by ring, Real.rpow_add hrpos,
        Real.rpow_neg_one]
      simp only [abs_of_nonneg (mul_nonneg hc (inv_nonneg.mpr hrpos.le))]
      field_simp]
    simp only [Real.norm_eq_abs, abs_div, abs_abs, abs_of_pos hrpos,
      abs_of_nonneg hnonneg]
    gcongr; exact hb_main r hr.le
  have habs0 : Tendsto (fun r => |q r|) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hc0
    · exact Filter.Eventually.of_forall fun r => abs_nonneg _
    · filter_upwards [eventually_ge_atTop r₀] with r hr
      exact hb_main r hr
  exact ⟨⟨hq, r₀, hr₀, hint⟩, tendsto_zero_iff_norm_tendsto_zero.mpr habs0⟩

/-- Difference between an eventually `O(1/r)` term and a logarithmically
integrable error remains a logarithmically integrable error. -/
theorem isLogErrorFunction_sub_of_denominator_bound {q : ℝ → ℝ} (hq : Measurable q)
    {c r₀ : ℝ} (hc : 0 ≤ c) (hr₀ : 0 < r₀)
    (hbound : ∀ r, r₀ ≤ r → |q r| ≤ c * r⁻¹)
    {δ : ℝ → ℝ} (hδ : IsLogErrorFunction δ) :
    IsLogErrorFunction (fun r => q r - δ r) := by
  have hq0 := isLogErrorFunction_of_denominator_bound hq hc hr₀ hbound
  have hn := isLogErrorFunction_neg hδ
  simpa only [sub_eq_add_neg] using isLogErrorFunction_add hq0 hn

#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_neg
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_of_denominator_bound
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_sub_of_denominator_bound

end PercLib.CriticalLRP.Analysis
