/-
# Logarithmic integrability of bounded first-moment errors

The final assertion of Lemma I.4.9: an eventually nonnegative measurable error
bounded by `c * r^(3α-d)` is logarithmically integrable when `d > 3α`. The
bootstrap that produces such a bound is a separate, deliberately unassumed unit.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_4_13

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.Analysis

open Filter MeasureTheory Set

open scoped Topology

/-- A measurable function eventually dominated by a negative power is a
logarithmically integrable error function. -/
theorem isLogErrorFunction_of_eventually_rpow_bound {E : ℝ → ℝ} (hmeas : Measurable E)
    {a c r₀ : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hr₀ : 0 < r₀)
    (hbound : ∀ r, r₀ ≤ r → 0 ≤ E r ∧ E r ≤ c * r ^ (-a)) :
    IsLogErrorFunction E := by
  have hg := isLogErrorFunction_const_rpow_neg (a := a) (c := c) (r₀ := r₀) ha hr₀
  obtain ⟨⟨hgm, R, hR, hintg⟩, hg0⟩ := hg
  have htail : IntegrableOn (fun r => |E r| / r) (Ioi (max r₀ R)) volume := by
    have hgground := hintg.mono_set (Ioi_subset_Ioi (le_max_right r₀ R))
    refine hgground.mono' ((hmeas.abs.div measurable_id).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : max r₀ R < r := hr
    have hr0 : 0 < r := (lt_max_of_lt_left hr₀).trans hr'
    have hE := hbound r (le_trans (le_max_left r₀ R) hr'.le)
    have hg0' : 0 ≤ c * r ^ (-a) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hE.1, abs_of_pos hr0,
      abs_of_nonneg hg0']
    exact div_le_div_of_nonneg_right
      (by simpa only [abs_of_nonneg hE.1] using hE.2) hr0.le
  refine ⟨⟨hmeas, max r₀ R, lt_max_of_lt_left hr₀, htail⟩, ?_⟩
  apply squeeze_zero' _ _ hg0
  · filter_upwards [eventually_ge_atTop r₀] with r hr
    exact (hbound r hr).1
  · filter_upwards [eventually_ge_atTop r₀] with r hr
    exact (hbound r hr).2

end PercLib.CriticalLRP.Analysis

namespace PercLib.CriticalLRP.VolumeMoments.FirstMoment

open Filter MeasureTheory Set

open scoped Topology

/-- **Final corollary of Lemma I.4.9.** Given its eventual explicit
`E₁,r` bound, `E₁,r` is logarithmically integrable. This declaration does not
assume or assert that the separate bootstrap producing the bound has been
completed. -/
theorem lemma_I_4_9_logIntegrable {E : ℝ → ℝ} {d α βc r₀ : ℝ}
    (hα : 0 < α) (hβc : 0 < βc) (hd : 3 * α < d) (hr₀ : 0 < r₀)
    (hmeas : Measurable E)
    (hbound : ∀ r, r₀ ≤ r → 0 ≤ E r ∧ E r ≤ 16 * α ^ 3 / βc ^ 3 * r ^ (3 * α - d)) :
    Analysis.IsLogErrorFunction E := by
  apply Analysis.isLogErrorFunction_of_eventually_rpow_bound hmeas
    (a := d - 3 * α) (c := 16 * α ^ 3 / βc ^ 3) (r₀ := r₀)
  · linarith
  · positivity
  · exact hr₀
  · intro r hr
    have hrpos : 0 < r := hr₀.trans_le hr
    have hexp : 3 * α - d = -(d - 3 * α) := by ring
    simpa only [hexp] using hbound r hr

end PercLib.CriticalLRP.VolumeMoments.FirstMoment
