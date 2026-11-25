/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.Analysis.Lemma_I_5_6

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory Real
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

/-- Karamata integration for a positive regularly varying function with its
logarithmic differential, normalized by the function itself. -/
theorem tendsto_logPrimitive_div_self {h : ℝ → ℝ} {b : ℝ} (D : RVPosData h b) :
    ∃ R : ℝ, 0 < R ∧
      Tendsto (fun r => (∫ s in R..r, h s / s) / h r) atTop (𝓝 (1 / b)) := by
  obtain ⟨R, hR, hlocal⟩ := exists_intervalIntegrable_tail_of_regularlyVarying
    D.pos_index D.measurable_f D.rv (by
      filter_upwards [eventually_ge_atTop D.threshold] with r hr
      exact D.pos_above r hr)
  let R₀ : ℝ := max 1 (max R D.threshold)
  have hR₀ : 0 < R₀ := by positivity
  have hR₀1 : 1 ≤ R₀ := le_max_left _ _
  have hRR₀ : R ≤ R₀ := (le_max_left R D.threshold).trans (le_max_right 1 _)
  have hDR₀ : D.threshold ≤ R₀ := (le_max_right R D.threshold).trans (le_max_right 1 _)
  let g : ℝ → ℝ := fun s => h s / s
  let T : ℝ → ℝ := (Ioi R₀).indicator g
  have hgm : Measurable g := D.measurable_f.div measurable_id
  have hTm : Measurable T := hgm.indicator measurableSet_Ioi
  have hTpos : ∀ᶠ x in atTop, 0 < T x := by
    filter_upwards [eventually_gt_atTop R₀] with x hx
    have hx0 : 0 < x := hR₀.trans hx
    simpa [T, g, hx] using div_pos (D.pos_above x (hDR₀.trans hx.le)) hx0
  have hgrv : RegularlyVaryingAtTop g (b - 1) := by
    have hh := D.rv.mul (regularlyVaryingAtTop_rpow 1).inv
    have hidx : b + -1 = b - 1 := by ring
    rw [hidx] at hh
    simpa [g, div_eq_mul_inv, Real.rpow_one] using hh
  have hTrv : RegularlyVaryingAtTop T (b - 1) := regularlyVarying_indicator_Ioi hgrv
  have hgint : ∀ x y : ℝ, R₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := D.bddAbove_Icc y
    have hh : IntervalIntegrable h volume x y := by
      apply intervalIntegrable_of_bound D.measurable_f.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
      rw [uIcc_of_le hxy] at hs
      rw [Real.norm_eq_abs, abs_of_pos (D.pos_above s ((hDR₀.trans hx).trans hs.1))]
      exact hC s ((hDR₀.trans hx).trans hs.1) hs.2
    have hIc : IntegrableOn h (Icc x y) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by finiteness)).1 hh
    have hcont : ContinuousOn (fun s : ℝ => s⁻¹) (Icc x y) := by
      apply continuousOn_id.inv₀
      intro s hs
      exact ((hR₀.trans_le hx).trans_le hs.1).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    simpa [g, div_eq_mul_inv] using hIc.mul_continuousOn hcont isCompact_Icc
  have hTloc : LocallyIntegrableOn T (Ioi 0) :=
    locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable hgint
  have hK : Tendsto (fun r => (∫ s in 1..r, T s) / (r * T r)) atTop (𝓝 (1 / b)) := by
    have hk := lemma_I_2_10_of_regularlyVarying (by linarith [D.pos_index] : -1 < b - 1)
      hTm hTloc hTpos hTrv
    convert hk using 1; ring
  refine ⟨R₀, hR₀, ?_⟩
  apply hK.congr'
  filter_upwards [eventually_gt_atTop R₀] with r hr
  have hseg : (∫ s in R₀..r, T s) = ∫ s in R₀..r, h s / s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [uIoc_of_le hr.le] at hx
    exact Set.indicator_of_mem hx.1 g
  have hrr : R₀ ≤ r := hr.le
  have htr : T r = h r / r := by
    show T r = g r
    exact Set.indicator_of_mem hr g
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_indicator_Ioi_of_intervalIntegrable
      (fun x y hx hxy => (hgint x y hx hxy).1) 1 R₀)
    (intervalIntegrable_indicator_Ioi_of_intervalIntegrable
      (fun x y hx hxy => (hgint x y hx hxy).1) R₀ r)
  have hzero : (∫ s in 1..R₀, T s) = 0 := by
    calc (∫ s in 1..R₀, T s) = ∫ s in 1..R₀, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hR₀1] at hx
          change T x = 0
          exact Set.indicator_of_notMem (fun hm => (not_lt_of_ge hx.2) hm) g
      _ = 0 := intervalIntegral.integral_zero
  rw [hzero, zero_add] at hadd
  rw [← hadd, htr, hseg]
  have hrpos : 0 < r := hR₀.trans hr
  have hpos := D.pos_above r (hDR₀.trans hr.le)
  field_simp [hrpos.ne', hpos.ne']

#print axioms PercLib.CriticalLRP.Analysis.tendsto_logPrimitive_div_self

end PercLib.CriticalLRP.Analysis
