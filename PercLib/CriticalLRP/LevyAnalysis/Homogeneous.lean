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
public import PercLib.CriticalLRP.LevyAnalysis.Radial
public import PercLib.CriticalLRP.LevyAnalysis.Rpow

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Metric Set Filter
open Module
open scoped ENNReal NNReal Topology Pointwise Interval

namespace PercLib.CriticalLRP.LevyAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Measurability of `t ↦ t ^ q` on `ℝ`. -/
theorem measurable_rpow_const' (q : ℝ) : Measurable (fun t : ℝ => t ^ q) := by
  fun_prop

/-- **Radial integration with a homogeneous weight.**
For `P` nonnegative, measurable and homogeneous of degree `k` (`P (c • x) = c ^ k * P x` for
`c > 0`) on a finite-dimensional real normed space of dimension `d` with additive Haar measure
`μ`, and for `0 < s < k + d`:

  `∫⁻ x in ball 0 R, P x * ‖x‖ ^ (-s) = ((k+d) / (k+d-s)) * R ^ (k+d-s) * ∫⁻ x in ball 0 1, P x`.

This is the "polar coordinates free" radial computation underlying the moments of the Lévy
measure `Π₁` of (I.5.16) and the Green function (Riesz kernel) bounds. -/
theorem lintegral_ball_hom_rpow (μ : Measure E) [μ.IsAddHaarMeasure] [Nontrivial E]
    {P : E → ℝ} (hP : ∀ x, 0 ≤ P x) (hPm : Measurable P) {k s : ℝ}
    (hhom : ∀ (c : ℝ), 0 < c → ∀ x, P (c • x) = c ^ k * P x)
    (hs : 0 < s) (hsk : s < k + (finrank ℝ E : ℝ)) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (P x * ‖x‖ ^ (-s)) ∂μ
      = ENNReal.ofReal ((k + (finrank ℝ E : ℝ)) / (k + (finrank ℝ E : ℝ) - s)
          * R ^ (k + (finrank ℝ E : ℝ) - s))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ := by
  have hdpos : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    have := Module.finrank_pos (R := ℝ) (M := E)
    exact_mod_cast this
  have hkds : (0 : ℝ) < k + (finrank ℝ E : ℝ) - s := by linarith
  -- the singleton `{0}` is null
  have hsing : μ ({(0 : E)} : Set E) = 0 := by
    have h := Measure.addHaar_smul μ (r := (0 : ℝ)) (s := (Set.univ : Set E))
    rw [zero_smul_set (Set.univ_nonempty (α := E)),
      zero_pow (Nat.pos_iff_ne_zero.mp (Module.finrank_pos (R := ℝ) (M := E))), abs_zero, ENNReal.ofReal_zero, zero_mul] at h
    exact h
  have haeμ : ∀ᵐ x ∂μ, x ≠ (0 : E) := by
    rw [MeasureTheory.ae_iff]
    simpa using hsing
  -- generic measurability
  have hg_meas : Measurable (fun t : ℝ => ENNReal.ofReal (s * t ^ (-s - 1))) :=
    (measurable_const.mul (measurable_rpow_const' (-s - 1))).ennreal_ofReal
  -- Step 1: the ball formula at all radii
  have hball : ∀ ρ : ℝ, 0 < ρ → ∫⁻ x in ball (0 : E) ρ, ENNReal.ofReal (P x) ∂μ
      = ENNReal.ofReal (ρ ^ (k + (finrank ℝ E : ℝ)))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ := by
    intro ρ hρ
    exact lintegral_ball_hom μ hP hPm hhom hρ
  -- Step 2: the pointwise decomposition, almost everywhere on the ball
  have hpt : ∀ᵐ x ∂(μ.restrict (ball (0 : E) R)),
      ENNReal.ofReal (P x * ‖x‖ ^ (-s))
        = ENNReal.ofReal (P x * R ^ (-s))
          + ∫⁻ t, (if ‖x‖ < t ∧ t ≤ R then
              ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1)) else 0) := by
    filter_upwards [ae_mono Measure.restrict_le_self haeμ, ae_restrict_mem measurableSet_ball]
      with x hx0 hxmem
    have hxR : ‖x‖ < R := by simpa [mem_ball, dist_zero_right] using hxmem
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hbase := ofReal_rpow_neg_eq_add_lintegral (s := s) (R := R) (a := ‖x‖) hs hxpos hxR.le
    have hmul : ENNReal.ofReal (P x) * ENNReal.ofReal (‖x‖ ^ (-s))
        = ENNReal.ofReal (P x) * ENNReal.ofReal (R ^ (-s))
          + ENNReal.ofReal (P x) * ∫⁻ t in Ioc ‖x‖ R,
              ENNReal.ofReal (s * t ^ (-s - 1)) := by
      rw [hbase, mul_add]
    rw [← ENNReal.ofReal_mul (hP x), ← ENNReal.ofReal_mul (hP x)] at hmul
    have hsupp_fun : (fun t => if ‖x‖ < t ∧ t ≤ R then
          ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1)) else 0)
        = (Ioc ‖x‖ R).indicator
            (fun t => ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1))) := by
      ext t; simp only [mem_Ioc, Set.indicator_apply]
    have hsupp : (∫⁻ t, (if ‖x‖ < t ∧ t ≤ R then
          ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1)) else 0))
        = ENNReal.ofReal (P x) * ∫⁻ t in Ioc ‖x‖ R,
            ENNReal.ofReal (s * t ^ (-s - 1)) := by
      rw [hsupp_fun, lintegral_indicator measurableSet_Ioc, lintegral_const_mul _ hg_meas]
    rw [hsupp, hmul]
  -- Step 3: integrate the decomposition
  rw [lintegral_congr_ae hpt]
  have hm1 : Measurable (fun a : E => ENNReal.ofReal (P a * R ^ (-s))) := by
    simpa only [Pi.mul_apply] using (hPm.mul_const (R ^ (-s))).ennreal_ofReal
  rw [lintegral_add_left hm1]
  -- Term 1
  have hterm1 : ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (P x * R ^ (-s)) ∂μ
      = ENNReal.ofReal (R ^ (-s)) * (ENNReal.ofReal (R ^ (k + (finrank ℝ E : ℝ)))
          * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) := by
    have hmul' : ∀ x : E, ENNReal.ofReal (P x * R ^ (-s))
        = ENNReal.ofReal (P x) * ENNReal.ofReal (R ^ (-s)) := fun x =>
      ENNReal.ofReal_mul (hP x)
    rw [lintegral_congr hmul', lintegral_mul_const _ hPm.ennreal_ofReal, hball R hR,
      mul_comm]
  -- Term 2: Tonelli
  set G : E → ℝ → ℝ≥0∞ := fun x t =>
    if ‖x‖ < t ∧ t ≤ R then ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1)) else 0 with hG
  have hG_meas : AEMeasurable (Function.uncurry G) (μ.prod volume) := by
    have huncurry : Function.uncurry G = fun p : E × ℝ =>
        if ‖p.1‖ < p.2 ∧ p.2 ≤ R then
          ENNReal.ofReal (P p.1) * ENNReal.ofReal (s * p.2 ^ (-s - 1)) else 0 := by
      funext p
      obtain ⟨x, t⟩ := p
      simp only [Function.uncurry_apply_pair, hG]
    rw [huncurry]
    refine Measurable.ite ?_ ?_ measurable_const |>.aemeasurable
    · exact (measurableSet_lt (measurable_norm.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    · exact ((hPm.comp measurable_fst).ennreal_ofReal).mul
        ((measurable_const.mul
          ((measurable_rpow_const' (-s - 1)).comp measurable_snd)).ennreal_ofReal)
  have hG_off : ∀ x : E, x ∉ ball (0 : E) R → ∀ t : ℝ, G x t = 0 := by
    intro x hx t
    simp only [hG]
    have h : ¬ (‖x‖ < t ∧ t ≤ R) := by
      rintro ⟨h1, h2⟩
      exact hx (by simpa [mem_ball, dist_zero_right] using lt_of_lt_of_le h1 h2)
    simp [h]
  have hterm2 : ∫⁻ x in ball (0 : E) R, (∫⁻ t, G x t) ∂μ
      = ∫⁻ t, ∫⁻ x, G x t ∂μ := by
    have h1 : ∫⁻ x in ball (0 : E) R, (∫⁻ t, G x t) ∂μ = ∫⁻ x, (∫⁻ t, G x t) ∂μ := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ ball (0 : E) R
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        simp only [hG_off x hx, lintegral_zero]
    rw [h1, lintegral_lintegral_swap (μ := μ) (ν := volume) hG_meas]
  -- compute the inner integral for each t
  have hinner : ∀ t : ℝ, (∫⁻ x, G x t ∂μ) = if 0 < t ∧ t ≤ R then
      ENNReal.ofReal (s * t ^ (-s - 1)) * (ENNReal.ofReal (t ^ (k + (finrank ℝ E : ℝ)))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) else 0 := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ R
    · rw [ite_eq_left ht]
      have hfun : ∀ x : E, G x t = (ball (0 : E) t).indicator
          (fun x => ENNReal.ofReal (P x) * ENNReal.ofReal (s * t ^ (-s - 1))) x := by
        intro x
        by_cases hx : x ∈ ball (0 : E) t
        · have h1 : ‖x‖ < t := by simpa [mem_ball, dist_zero_right] using hx
          rw [hG]
          simp only [h1, ht.2, and_self, ite_eq_left, indicator_of_mem hx]
        · have h1 : ¬ (‖x‖ < t) := by simpa [mem_ball, dist_zero_right] using hx
          rw [hG]
          simp only [h1, false_and, ite_false, indicator_of_notMem hx]
      rw [lintegral_congr hfun, lintegral_indicator measurableSet_ball,
        lintegral_mul_const _ hPm.ennreal_ofReal, hball t ht.1, mul_comm]
    · rw [ite_eq_right ht]
      have hzero : ∀ x : E, G x t = 0 := by
        intro x
        rw [hG]
        by_cases h : ‖x‖ < t ∧ t ≤ R
        · exact absurd ⟨lt_of_le_of_lt (norm_nonneg x) h.1, h.2⟩ ht
        · simp [h]
      simp [hzero]
  rw [hterm1, hterm2, lintegral_congr hinner]
  -- the remaining 1-D computation
  have h1d : ∀ t : ℝ, (if 0 < t ∧ t ≤ R then
      ENNReal.ofReal (s * t ^ (-s - 1)) * (ENNReal.ofReal (t ^ (k + (finrank ℝ E : ℝ)))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) else 0)
      = (Ioc (0 : ℝ) R).indicator (fun t =>
          ENNReal.ofReal (s * t ^ (k + (finrank ℝ E : ℝ) - s - 1))
            * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) t := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) R
    · rw [indicator_of_mem ht, ite_eq_left ⟨ht.1, ht.2⟩]
      have hexp : -s - 1 + (k + (finrank ℝ E : ℝ)) = k + (finrank ℝ E : ℝ) - s - 1 := by ring
      rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hs.le (Real.rpow_nonneg ht.1.le _)),
        mul_assoc s, ← Real.rpow_add ht.1, hexp]
    · rw [indicator_of_notMem ht, ite_eq_right]
      intro h; exact ht ⟨h.1, h.2⟩
  have hm2 : Measurable (fun a : ℝ =>
      ENNReal.ofReal (s * a ^ (k + (finrank ℝ E : ℝ) - s - 1))) := by
    simpa only [Pi.mul_apply] using
      (measurable_const.mul (measurable_rpow_const' (k + (finrank ℝ E : ℝ) - s - 1))).ennreal_ofReal
  have hm3 : Measurable (fun a : ℝ =>
      ENNReal.ofReal (a ^ (k + (finrank ℝ E : ℝ) - s - 1))) :=
    (measurable_rpow_const' _).ennreal_ofReal
  have hsplit : (∫⁻ a in Ioc (0 : ℝ) R,
      ENNReal.ofReal (s * a ^ (k + (finrank ℝ E : ℝ) - s - 1)))
      = ENNReal.ofReal s * ∫⁻ a in Ioc (0 : ℝ) R,
          ENNReal.ofReal (a ^ (k + (finrank ℝ E : ℝ) - s - 1)) := by
    rw [← lintegral_const_mul (ENNReal.ofReal s) hm3]
    apply lintegral_congr
    intro a
    rw [ENNReal.ofReal_mul hs.le]
  rw [lintegral_congr h1d, lintegral_indicator measurableSet_Ioc,
    lintegral_mul_const _ hm2, hsplit,
    lintegral_Ioc_zero_rpow (by linarith) hR.le]
  -- final arithmetic
  have hRs : R ^ (-s) * R ^ (k + (finrank ℝ E : ℝ)) = R ^ (k + (finrank ℝ E : ℝ) - s) := by
    rw [← Real.rpow_add hR]
    norm_num [show -s + (k + (finrank ℝ E : ℝ)) = k + (finrank ℝ E : ℝ) - s from by ring]
  have hb : (0 : ℝ) ≤ s * (R ^ (k + (finrank ℝ E : ℝ) - s - 1 + 1)
      / (k + (finrank ℝ E : ℝ) - s - 1 + 1)) := by
    have h1 : (0 : ℝ) < R ^ (k + (finrank ℝ E : ℝ) - s - 1 + 1) := Real.rpow_pos_of_pos hR _
    have h2 : (0 : ℝ) < k + (finrank ℝ E : ℝ) - s - 1 + 1 := by linarith
    positivity
  have hq : (k + (finrank ℝ E : ℝ) - s - 1 + 1) = k + (finrank ℝ E : ℝ) - s := by ring
  have hreal : R ^ (-s) * R ^ (k + (finrank ℝ E : ℝ))
      + s * (R ^ (k + (finrank ℝ E : ℝ) - s - 1 + 1)
          / (k + (finrank ℝ E : ℝ) - s - 1 + 1))
      = (k + (finrank ℝ E : ℝ)) / (k + (finrank ℝ E : ℝ) - s)
          * R ^ (k + (finrank ℝ E : ℝ) - s) := by
    rw [hq, hRs]
    have hK : k + (finrank ℝ E : ℝ) - s ≠ 0 := by linarith
    field_simp
    ring
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hR (-s)).le,
    ← ENNReal.ofReal_mul hs.le, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) hb, hreal]

end PercLib.CriticalLRP.LevyAnalysis
