/- Integrated from independently rebuilt Ultramath work.
Production base 6b7eb1107b03297e4df33585eeac818682adb1d2.
Scratch source: repository-root .ultramath/smwwp7q3k/m2/.
-/

/-
# Lemma I.5.6: analytic helpers for the two-driver interface

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.5.6 (pp. 56-57).

This file contains no new definitions; it isolates three analytic facts used by
`TwoDrivers.lean` and `Driver.lean`:

* `logarithmicallyIntegrable_mul_of_tendsto_pos` — multiplication by a function
  tending to a positive limit preserves logarithmic integrability (the paper's
  "shares the logarithmic integrability properties ... after multiplication by
  `r ^ (-a)`");
* `intervalIntegrable_div_rpow_succ` — `s ↦ g s / s ^ (a+1)` is interval
  integrable on any interval above the regular-variation threshold of `g`;
* `tendsto_intervalIntegral_div_shift` — a limit of ratios of divergent interval
  integrals is unchanged by moving the base point of the integrals.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_5_6

/-! Analytic helpers for the precise second-driver comparison in Lemma I.5.6. -/

/-! Analytic lemmas for replacing a regularly varying second driver. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

@[expose] public section

open Filter Set MeasureTheory Real
open scoped Topology

namespace PercLib.CriticalLRP.Analysis.I56Driver

/-- Multiplication by a function tending to a positive limit preserves
logarithmic integrability. -/
theorem logarithmicallyIntegrable_mul_of_tendsto_pos {u E : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hlim : Tendsto E atTop (𝓝 A)) (hu : LogarithmicallyIntegrable u) (hEm : Measurable E) :
    LogarithmicallyIntegrable (fun s => u s * E s) := by
  obtain ⟨hum, r₀, hr₀, hint⟩ := hu
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hlim 1 one_pos
  have hR0 : 0 < max r₀ B := lt_max_of_lt_left hr₀
  refine ⟨hum.mul hEm, max r₀ B, hR0, ?_⟩
  have hbase : IntegrableOn (fun s => (A + 1) * (|u s| / s)) (Ioi (max r₀ B)) volume :=
    (hint.mono_set (Ioi_subset_Ioi (le_max_left r₀ B))).const_mul (A + 1)
  apply hbase.mono' (((hum.mul hEm).abs).div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hR0.trans hs
  have hb := hB s ((le_max_right r₀ B).trans hs.le)
  rw [Real.dist_eq] at hb
  have hb' := abs_lt.1 hb
  have hE : |E s| ≤ A + 1 := by
    have h1 : |E s| ≤ |E s - A| + |A| := by
      calc |E s| = |(E s - A) + A| := by ring_nf
        _ ≤ |E s - A| + |A| := abs_add_le _ _
    have h2 : |A| = A := abs_of_pos hA
    linarith [h1, hb, h2]
  simp only [Pi.mul_apply, Pi.div_apply, id_eq]
  change ‖|u s * E s| / s‖ ≤ (A + 1) * (|u s| / s)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) hs0.le), abs_mul]
  calc |u s| * |E s| / s ≤ |u s| * (A + 1) / s :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (abs_nonneg _)) hs0.le
    _ = (A + 1) * (|u s| / s) := by field_simp

/-- `s ↦ g s / s ^ (ρ + 1)` is interval integrable on any interval lying above
the regular-variation threshold of `g`. -/
theorem intervalIntegrable_div_rpow_succ {g : ℝ → ℝ} {ρ : ℝ} (D : RVPosData g ρ)
    {x y : ℝ} (hx : D.threshold ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun s => g s / s ^ (ρ + 1)) volume x y := by
  have hx0 : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le one_pos D.one_le_threshold) hx
  obtain ⟨C, hC⟩ := D.bddAbove_Icc y
  have hh : IntervalIntegrable g volume x y :=
    intervalIntegrable_of_bound (C := C) D.measurable_f.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
      rw [uIcc_of_le hxy] at hs
      rw [Real.norm_eq_abs, abs_of_pos (D.pos_above s (hx.trans hs.1))]
      exact hC s (hx.trans hs.1) hs.2)
  have hIc : IntegrableOn g (Icc x y) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)).1 hh
  have hcont : ContinuousOn (fun s : ℝ => (s ^ (ρ + 1))⁻¹) (Icc x y) := by
    apply ContinuousOn.inv₀
    · intro s hs
      exact (Real.continuousAt_rpow_const s (ρ + 1)
        (Or.inl ((hx0.trans_le hs.1).ne'))).continuousWithinAt
    · intro s hs
      exact (Real.rpow_pos_of_pos (hx0.trans_le hs.1) (ρ + 1)).ne'
  have hgoal : IntegrableOn (fun s => g s / s ^ (ρ + 1)) (Icc x y) volume := by
    simpa [div_eq_mul_inv] using hIc.mul_continuousOn hcont isCompact_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)).2 hgoal

/-- The elementary algebraic identity behind the shift of the base point. -/
theorem shift_ratio_identity (N D AF AG : ℝ) (hD : D ≠ 0) (hDAG : D - AG ≠ 0) :
    (N - AF) / (D - AG) = (N / D - AF / D) / (1 - AG / D) := by
  field_simp

/-- A limit of ratios of divergent interval integrals does not depend on the base
point of the integrals, as long as both integrands are interval integrable from
the smaller base point. -/
theorem tendsto_intervalIntegral_div_shift {F G : ℝ → ℝ} {x₀ r₀ C : ℝ} (hC : 0 < C)
    (hxr : x₀ ≤ r₀)
    (hF : ∀ x y : ℝ, x₀ ≤ x → x ≤ y → IntervalIntegrable F volume x y)
    (hG : ∀ x y : ℝ, x₀ ≤ x → x ≤ y → IntervalIntegrable G volume x y)
    (hGtop : Tendsto (fun r => ∫ s in r₀..r, G s) atTop atTop)
    (hcmp : Tendsto (fun r => (∫ s in x₀..r, F s) / (∫ s in x₀..r, G s)) atTop (𝓝 C)) :
    Tendsto (fun r => (∫ s in r₀..r, F s) / (∫ s in r₀..r, G s)) atTop (𝓝 C) := by
  classical
  set AF : ℝ := ∫ s in x₀..r₀, F s with hAF
  set AG : ℝ := ∫ s in x₀..r₀, G s with hAG
  have hDtop : Tendsto (fun r => ∫ s in x₀..r, G s) atTop atTop := by
    have hEq : (fun r => ∫ s in x₀..r, G s)
        =ᶠ[atTop] (fun r => (∫ s in r₀..r, G s) + AG) := by
      filter_upwards [eventually_ge_atTop r₀] with r hr
      have h := intervalIntegral.integral_add_adjacent_intervals
        (hG x₀ r₀ le_rfl hxr) (hG r₀ r hxr hr)
      rw [← h, hAG]
      ring
    exact (tendsto_atTop_add_const_right atTop AG hGtop).congr' hEq.symm
  have hnum : Tendsto
      (fun r => (∫ s in x₀..r, F s) / (∫ s in x₀..r, G s) - AF / (∫ s in x₀..r, G s))
      atTop (𝓝 (C - 0)) :=
    hcmp.sub (tendsto_const_nhds.div_atTop hDtop)
  rw [sub_zero] at hnum
  have hden : Tendsto (fun r => 1 - AG / (∫ s in x₀..r, G s)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hDtop)
  rw [sub_zero] at hden
  have hdenne : ∀ᶠ r in atTop, (1 - AG / (∫ s in x₀..r, G s)) ≠ 0 := by
    have h0 : Tendsto (fun r => AG / (∫ s in x₀..r, G s)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hDtop
    filter_upwards [h0.eventually (eventually_lt_nhds zero_lt_one)] with r hr
    intro hzero
    linarith
  have hdiv := hnum.div hden one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop r₀,
    hDtop.eventually (eventually_gt_atTop (max AG 0))] with r hr hAGD
  have hDgt : AG < ∫ s in x₀..r, G s := lt_of_le_of_lt (le_max_left AG 0) hAGD
  have hDpos : (0:ℝ) < ∫ s in x₀..r, G s := lt_of_le_of_lt (le_max_right AG 0) hAGD
  have eF : ∫ s in r₀..r, F s = (∫ s in x₀..r, F s) - AF := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hF x₀ r₀ le_rfl hxr) (hF r₀ r hxr hr)
    rw [hAF]
    linarith
  have eG : ∫ s in r₀..r, G s = (∫ s in x₀..r, G s) - AG := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (hG x₀ r₀ le_rfl hxr) (hG r₀ r hxr hr)
    rw [hAG]
    linarith
  rw [eF, eG]
  exact (shift_ratio_identity (∫ s in x₀..r, F s) (∫ s in x₀..r, G s) AF AG hDpos.ne'
    (by linarith)).symm

/-- The final comparison step of the logarithmic corollary of Lemma I.5.6: the
divergent-branch limit `f r ∼ r ^ a ∫ h s / s ^ (a+1)` together with
`h r ∼ A r ^ a` gives `f r ∼ A r ^ a log r`. -/
theorem log_corollary_of_divergent_branch {f h : ℝ → ℝ} {a A r₀ : ℝ} (hA : 0 < A)
    (hr₀ : 0 < r₀)
    (hUint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y)
    (hmain : Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1)))
      atTop (𝓝 1))
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (A * r ^ a * Real.log r)) atTop (𝓝 1) := by
  let U : ℝ → ℝ := fun s => h s / s ^ (a + 1)
  have hUA : Tendsto (fun s => U s / (A / s)) atTop (𝓝 1) := by
    apply hhA.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    dsimp [U]
    rw [Real.rpow_add hs, Real.rpow_one]
    field_simp [hA.ne', hs.ne', (Real.rpow_pos_of_pos hs a).ne']
  have hUlog := tendsto_intervalIntegral_div_mul_log hr₀ hA hUA hUint
  have hmul := hmain.mul hUlog
  rw [mul_one] at hmul
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (max r₀ 1),
    hUlog.eventually (eventually_gt_nhds zero_lt_one)] with r hr hratio
  have hrr₀ : r₀ < r := (le_max_left _ _).trans_lt hr
  have hr1 : 1 < r := (le_max_right _ _).trans_lt hr
  have hr0 : 0 < r := hr₀.trans hrr₀
  have hrlog : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr1)
  have hden : 0 < A * Real.log r := mul_pos hA (Real.log_pos hr1)
  have hIU : 0 < ∫ s in r₀..r, U s := (div_pos_iff_of_pos_right hden).mp hratio
  change f r / (r ^ a * ∫ s in r₀..r, U s) * ((∫ s in r₀..r, U s) / (A * Real.log r)) =
    f r / (A * r ^ a * Real.log r)
  field_simp [hA.ne', hrlog, hIU.ne', (Real.rpow_pos_of_pos hr0 a).ne']

end PercLib.CriticalLRP.Analysis.I56Driver

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Analysis.I56Driver.logarithmicallyIntegrable_mul_of_tendsto_pos
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.intervalIntegrable_div_rpow_succ
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.tendsto_intervalIntegral_div_shift
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.log_corollary_of_divergent_branch
