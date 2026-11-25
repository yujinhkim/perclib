/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.5.6: critical effects from a logarithmically integrable ODE error

The reduced independent-error ODE, the two-error wrapper used by the source,
and the logarithmic asymptotic corollaries. Logarithmic integral divergence is
handled through explicit improper-integral comparisons, without an additional
logarithmic Cesàro hypothesis.
-/
module

public import PercLib.CriticalLRP.Analysis.CriticalLog

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

/-- **Lemma I.5.6 in the reduced form** used by the paper: the homogeneous
error is measurable and logarithmically integrable, and the inhomogeneous term
is unweighted. -/
theorem lemma_I_5_6_reduced {f f' h δ : ℝ → ℝ} {a R : ℝ} (ha : 0 < a)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h a)
    (hpos : ∀ᶠ x in atTop, 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ : IsLogErrorFunction δ)
    (hode : ∀ x, 0 < x → f' x = (1 - δ x) * a * f x / x + h x / x) :
    ∃ r₀ : ℝ, R ≤ r₀ ∧ 0 < r₀ ∧
      (∀ x y : ℝ, r₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      ((¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1)))
          atTop (𝓝 1)) ∧
      (LogarithmicallyIntegrable (fun r => h r / r ^ a) →
        ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A)) := by
  have hhe : ∀ᶠ x in atTop, 0 < h x := hpos
  let D : RVPosData h a := RVPosData.of ha hhm hhrv hhe
  have hδm : Measurable δ := hδ.1.1
  have hδ0 : Tendsto δ atTop (𝓝 0) := hδ.2
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hδ0 1 one_pos
  let r₀ : ℝ := max R (max (max 1 D.threshold) B)
  have hrR : R ≤ r₀ := le_max_left _ _
  have hr₀1 : 1 ≤ r₀ := ((le_max_left 1 D.threshold).trans
    (le_max_left (max 1 D.threshold) B)).trans (le_max_right R _)
  have hr₀ : 0 < r₀ := zero_lt_one.trans_le hr₀1
  have hrD : D.threshold ≤ r₀ := ((le_max_right 1 D.threshold).trans
    (le_max_left (max 1 D.threshold) B)).trans (le_max_right R _)
  have hrB : B ≤ r₀ := (le_max_right (max 1 D.threshold) B).trans (le_max_right R _)
  have hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1 := by
    intro x hx
    have hb := hB x (hrB.trans hx)
    rw [Real.dist_eq, sub_zero] at hb
    linarith
  let w := powerExpWeight r₀ a δ
  let E : ℝ → ℝ := fun r => w r / r ^ a
  let v : ℝ → ℝ := fun s => h s / w s
  let u : ℝ → ℝ := fun r => h r / r ^ a
  let U : ℝ → ℝ := fun s => h s / s ^ (a + 1)
  let g : ℝ → ℝ := fun s => v s / s
  let F : ℝ → ℝ := fun s => g s
  let q : ℝ → ℝ := fun r => f r * (w r)⁻¹
  have hwm : Measurable w := measurable_powerExpWeight hr₀ hδm hδ1
  have hwpos : ∀ s, 0 < s → 0 < w s := by
    intro s hs
    dsimp [w, powerExpWeight]
    exact mul_pos (Real.rpow_pos_of_pos hs a) (Real.exp_pos _)
  have hum : Measurable u := hhm.div (by fun_prop)
  have hvm : Measurable v := hhm.div hwm
  have hgm : Measurable g := hvm.div measurable_id
  have hEm : Measurable E := hwm.div (by fun_prop)
  have hUm : Measurable U := hhm.div (by fun_prop)
  obtain ⟨A, hA, hElim⟩ := tendsto_powerExpWeight_div_rpow hr₀ hδm hδ1 hδ.1
  have hEpos : ∀ x, 0 < x → 0 < E x := by
    intro x hx
    exact div_pos (hwpos x hx) (Real.rpow_pos_of_pos hx a)
  have hvpos : ∀ x, r₀ ≤ x → 0 < v x := by
    intro x hx
    exact div_pos (D.pos_above x (hrD.trans hx)) (hwpos x (hr₀.trans_le hx))
  have hgpos : ∀ x, r₀ ≤ x → 0 < g x := by
    intro x hx
    exact div_pos (hvpos x hx) (hr₀.trans_le hx)
  have hupos : ∀ x, r₀ ≤ x → 0 < u x := by
    intro x hx
    exact div_pos (D.pos_above x (hrD.trans hx))
      (Real.rpow_pos_of_pos (hr₀.trans_le hx) a)
  have hUpos : ∀ x, r₀ ≤ x → 0 < U x := by
    intro x hx
    exact div_pos (D.pos_above x (hrD.trans hx))
      (Real.rpow_pos_of_pos (hr₀.trans_le hx) (a + 1))
  have hU_u : ∀ x, 0 < x → U x = u x / x := by
    intro x hx
    dsimp [U, u]
    rw [Real.rpow_add hx, Real.rpow_one]
    ring
  have hwcont : ContinuousOn w (Ici r₀) := by
    intro s hs
    have hs0 : 0 < s := hr₀.trans_le hs
    have he : ContinuousAt (fun r => Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) s := by
      apply Real.continuous_exp.continuousAt.comp
      exact ((continuous_errorIntegral hr₀ hδm hδ1).continuousAt.const_mul a).neg
    change ContinuousWithinAt
      (fun r => r ^ a * Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) (Ici r₀) s
    have hfun : (fun r : ℝ => r ^ a * Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) =
        (fun r => r ^ a) * (fun r => Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) := by rfl
    rw [hfun]
    exact ((Real.continuousAt_rpow_const s a (Or.inl hs0.ne')).mul he).continuousWithinAt
  have hgint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := D.bddAbove_Icc y
    have hh : IntervalIntegrable h volume x y := by
      apply intervalIntegrable_of_bound hhm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
      rw [uIcc_of_le hxy] at hs
      rw [Real.norm_eq_abs, abs_of_pos (D.pos_above s ((hrD.trans hx).trans hs.1))]
      exact hC s ((hrD.trans hx).trans hs.1) hs.2
    have hIc : IntegrableOn h (Icc x y) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by finiteness)).1 hh
    have hcont : ContinuousOn (fun s => (s * w s)⁻¹) (Icc x y) := by
      apply (continuousOn_id.mul (hwcont.mono (fun s hs => hx.trans hs.1))).inv₀
      intro s hs
      have hs0 : 0 < s := (hr₀.trans_le hx).trans_le hs.1
      exact (mul_pos hs0 (hwpos s hs0)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    simpa [g, v, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hIc.mul_continuousOn hcont isCompact_Icc
  have hUint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable U volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := D.bddAbove_Icc y
    have hh : IntervalIntegrable h volume x y := by
      apply intervalIntegrable_of_bound hhm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
      rw [uIcc_of_le hxy] at hs
      rw [Real.norm_eq_abs, abs_of_pos (D.pos_above s ((hrD.trans hx).trans hs.1))]
      exact hC s ((hrD.trans hx).trans hs.1) hs.2
    have hIc : IntegrableOn h (Icc x y) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by finiteness)).1 hh
    have hcont : ContinuousOn (fun s : ℝ => (s ^ (a + 1))⁻¹) (Icc x y) := by
      apply ContinuousOn.inv₀
      · intro s hs
        exact (Real.continuousAt_rpow_const s (a + 1)
          (Or.inl ((hr₀.trans_le (hx.trans hs.1)).ne'))).continuousWithinAt
      · intro s hs
        exact (Real.rpow_pos_of_pos ((hr₀.trans_le hx).trans_le hs.1) (a + 1)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    simpa [U, div_eq_mul_inv] using hIc.mul_continuousOn hcont isCompact_Icc
  have hFint_of_le : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable F volume x y := by
    intro x y hx hxy
    simpa [F] using hgint x y hx hxy
  have hFint : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → IntervalIntegrable F volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · exact hFint_of_le x y hx hxy
    · exact (hFint_of_le y x hy hyx).symm
  have hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, F s := by
    intro R hR
    simpa [q, F, g, v, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      normalized_increment_of_driving_ode_unweighted (D := D) (a := a) (r₀ := r₀) (R := R)
        ha hr₀ hR hrD (fun x hx => hderiv x (hr₀.trans_le hx)) hδm hδ1
          (fun x hx => hode x (hr₀.trans_le hx))
  have hq₀ : 0 < q r₀ := by
    dsimp [q]
    exact mul_pos (hfpos r₀ hr₀) (inv_pos.mpr (hwpos r₀ hr₀))
  have huv : (fun r => u r / E r) =ᶠ[atTop] v := by
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hr0 : 0 < r := hr₀.trans_le hr
    dsimp [u, E, v]
    field_simp [(Real.rpow_pos_of_pos hr0 a).ne', (hwpos r hr0).ne']
  have hlogv : LogarithmicallyIntegrable u → LogarithmicallyIntegrable v := by
    intro hu
    exact (logarithmicallyIntegrable_div_of_tendsto_pos hA hElim hu hEm).congr_of_eventuallyEq
      huv hvm
  have hloginv : LogarithmicallyIntegrable v → LogarithmicallyIntegrable u := by
    intro hv
    have hliminv : Tendsto (fun r => (E r)⁻¹) atTop (𝓝 A⁻¹) := hElim.inv₀ hA.ne'
    have huvi : (fun r => v r / (E r)⁻¹) =ᶠ[atTop] u := by
      filter_upwards [eventually_ge_atTop r₀, huv] with r hr heq
      have hr0 : 0 < r := hr₀.trans_le hr
      rw [← heq]
      simp only [div_eq_mul_inv, inv_inv]
      field_simp [(hEpos r hr0).ne']
    have hlogi := logarithmicallyIntegrable_div_of_tendsto_pos (inv_pos.mpr hA)
      hliminv hv hEm.inv
    exact hlogi.congr_of_eventuallyEq huvi hum
  refine ⟨r₀, hrR, hr₀, hUint, ?_, ?_⟩
  · intro hnot
    change ¬ LogarithmicallyIntegrable u at hnot
    change Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, U s)) atTop (𝓝 1)
    have hnotv : ¬ LogarithmicallyIntegrable v := fun hv => hnot (hloginv hv)
    have hnotg : ¬ IntegrableOn g (Ioi r₀) volume := by
      intro hgi
      apply hnotv
      refine ⟨hvm, r₀, hr₀, ?_⟩
      apply hgi.congr_fun _ measurableSet_Ioi
      intro s hs
      have hs0 : 0 < s := hr₀.trans hs
      have hsr₀ : r₀ ≤ s := hs.le
      change g s = |v s| / s
      dsimp [g]
      rw [abs_of_pos (hvpos s hsr₀)]
    have hGinf : Tendsto (fun r => ∫ s in r₀..r, g s) atTop atTop :=
      tendsto_intervalIntegral_atTop_of_not_integrableOn (fun x y hx hxy => hgint x y hx hxy)
        (fun x hx => (hgpos x hx).le) hnotg
    have hFGratio : Tendsto (fun r => F r / g r) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop r₀] with r hr
      change 1 = g r / g r
      exact (div_self (hgpos r hr).ne').symm
    have hIFG := tendsto_intervalIntegral_div_of_tendsto_ratio hgpos hFGratio
      (fun x y hx hxy => hFint_of_le x y hx hxy) (fun x y hx hxy => hgint x y hx hxy) hGinf
    have hqdiff : Tendsto (fun r => (q r - q r₀) / (∫ s in r₀..r, g s)) atTop (𝓝 1) := by
      apply hIFG.congr'
      filter_upwards [eventually_ge_atTop r₀] with r hr
      rw [hqinc r hr]
    have hzero : Tendsto (fun r => q r₀ / (∫ s in r₀..r, g s)) atTop (𝓝 0) := by
      have hi := hGinf.inv_tendsto_atTop.const_mul (q r₀)
      simpa [div_eq_mul_inv] using hi
    have hsum := hqdiff.add hzero
    rw [add_zero] at hsum
    have hqG : Tendsto (fun r => q r / (∫ s in r₀..r, g s)) atTop (𝓝 1) := by
      apply hsum.congr'
      filter_upwards [eventually_ge_atTop r₀,
        hGinf.eventually (eventually_gt_atTop 0)] with r hr hrG
      field_simp [hrG.ne']
      ring
    have hnotU : ¬ IntegrableOn U (Ioi r₀) volume := by
      intro hUi
      apply hnot
      refine ⟨hum, r₀, hr₀, ?_⟩
      apply hUi.congr_fun _ measurableSet_Ioi
      intro s hs
      have hs0 : 0 < s := hr₀.trans hs
      have hsr₀ : r₀ ≤ s := hs.le
      change U s = |u s| / s
      rw [hU_u s hs0, abs_of_pos (hupos s hsr₀)]
    have hUinf : Tendsto (fun r => ∫ s in r₀..r, U s) atTop atTop :=
      tendsto_intervalIntegral_atTop_of_not_integrableOn (fun x y hx hxy => hUint x y hx hxy)
        (fun x hx => (hUpos x hx).le) hnotU
    have hliminv : Tendsto (fun r => (E r)⁻¹) atTop (𝓝 A⁻¹) := hElim.inv₀ hA.ne'
    have hgU : Tendsto (fun r => g r / U r) atTop (𝓝 A⁻¹) := by
      apply hliminv.congr'
      filter_upwards [eventually_ge_atTop r₀, huv] with r hr heq
      have hr0 : 0 < r := hr₀.trans_le hr
      rw [hU_u r hr0]
      dsimp [g]
      rw [← heq]
      field_simp [(hEpos r hr0).ne', (hupos r hr).ne', hr0.ne']
    have hGU := tendsto_intervalIntegral_div_of_tendsto_ratio hUpos hgU
      (fun x y hx hxy => hgint x y hx hxy) (fun x y hx hxy => hUint x y hx hxy) hUinf
    have hqUprod := hqG.mul hGU
    rw [one_mul] at hqUprod
    have hqU : Tendsto (fun r => q r / (∫ s in r₀..r, U s)) atTop (𝓝 A⁻¹) := by
      apply hqUprod.congr'
      filter_upwards [hGinf.eventually (eventually_gt_atTop 0),
        hUinf.eventually (eventually_gt_atTop 0)] with r hrG hrU
      field_simp [hrG.ne', hrU.ne']
    have hmul := hElim.mul hqU
    have hconst : A * A⁻¹ = 1 := by field_simp [hA.ne']
    rw [hconst] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop r₀,
      hUinf.eventually (eventually_gt_atTop 0)] with r hr hrU
    have hr0 : 0 < r := hr₀.trans_le hr
    have hf : f r = w r * q r := by
      dsimp [q]
      field_simp [(hwpos r hr0).ne']
    rw [hf]
    field_simp [(Real.rpow_pos_of_pos hr0 a).ne', hrU.ne']
    ring
  · intro hulog
    change LogarithmicallyIntegrable u at hulog
    have hvlog : LogarithmicallyIntegrable v := hlogv hulog
    have hIg : IntegrableOn g (Ioi r₀) volume :=
      integrableOn_div_of_logarithmicallyIntegrable hr₀ hvpos
        (fun x y hx hxy => by simpa [g] using hgint x y hx hxy) hvlog
    have hIF : IntegrableOn F (Ioi r₀) volume := by
      simpa [F] using hIg
    have hlimint : Tendsto (fun r => ∫ s in r₀..r, F s) atTop
        (𝓝 (∫ s in Ioi r₀, F s)) :=
      intervalIntegral_tendsto_integral_Ioi r₀ hIF tendsto_id
    have hdiff : Tendsto (fun r => q r - q r₀) atTop (𝓝 (∫ s in Ioi r₀, F s)) :=
      hlimint.congr' (by
        filter_upwards [eventually_ge_atTop r₀] with r hr
        exact (hqinc r hr).symm)
    have hlimq : Tendsto q atTop (𝓝 (q r₀ + ∫ s in Ioi r₀, F s)) := by
      simpa using hdiff.const_add (q r₀)
    have htail : 0 ≤ ∫ s in Ioi r₀, F s := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hsr₀ : r₀ ≤ s := hs.le
      change 0 ≤ g s
      exact (hgpos s hsr₀).le
    have hQpos : 0 < q r₀ + ∫ s in Ioi r₀, F s := add_pos_of_pos_of_nonneg hq₀ htail
    have hmul := hElim.mul hlimq
    refine ⟨A * (q r₀ + ∫ s in Ioi r₀, F s), mul_pos hA hQpos, ?_⟩
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hr0 : 0 < r := hr₀.trans_le hr
    have hf : f r = w r * q r := by
      dsimp [q]
      field_simp [(hwpos r hr0).ne']
    rw [hf]
    field_simp [(Real.rpow_pos_of_pos hr0 a).ne']
    ring

/-- **Logarithmic corollary of Lemma I.5.6.** If `h(r) ∼ A r^a`, then the
critical solution satisfies `f(r) ∼ A r^a log r`. -/
theorem lemma_I_5_6_log_of_tendsto {f f' h δ : ℝ → ℝ} {a A : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hhm : Measurable h)
    (hhrv : RegularlyVaryingAtTop h a) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ : IsLogErrorFunction δ)
    (hode : ∀ x, 0 < x → f' x = (1 - δ x) * a * f x / x + h x / x)
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (A * r ^ a * Real.log r)) atTop (𝓝 1) := by
  let u : ℝ → ℝ := fun r => h r / r ^ a
  have huA : Tendsto (fun r => u r / A) atTop (𝓝 1) := by
    apply hhA.congr'
    filter_upwards with r
    dsimp [u]
    ring
  have hulim : Tendsto u atTop (𝓝 A) := by
    have hm := huA.const_mul A
    rw [mul_one] at hm
    apply hm.congr'
    filter_upwards with r
    dsimp [u]
    field_simp [hA.ne']
  have hnot : ¬ LogarithmicallyIntegrable (fun r => h r / r ^ a) := by
    exact not_logarithmicallyIntegrable_of_tendsto_pos hA hulim
  have hhe : ∀ᶠ x in atTop, 0 < h x := hpos
  obtain ⟨r₀, _, hr₀, hUint, hnon, _⟩ := lemma_I_5_6_reduced (R := 0) ha hhm hhrv hhe hfpos hderiv hδ hode
  have hmain := hnon hnot
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
  have hIU : 0 < ∫ s in r₀..r, U s :=
    (div_pos_iff_of_pos_right hden).mp hratio
  change f r / (r ^ a * ∫ s in r₀..r, U s) * ((∫ s in r₀..r, U s) / (A * Real.log r)) =
    f r / (A * r ^ a * Real.log r)
  field_simp [hA.ne', hrlog, hIU.ne', (Real.rpow_pos_of_pos hr0 a).ne']

/-- **Lemma I.5.6 with both errors.** The source's reduction uses the explicit
hypotheses that the second error is measurable and tends to zero. -/
theorem lemma_I_5_6_of_errors {f f' h δ₁ δ₂ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h a)
    (hpos : ∀ᶠ x in atTop, 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂m : Measurable δ₂) (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ x, 0 < x →
      f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ x y : ℝ, r₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      ((¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1)))
          atTop (𝓝 1)) ∧
      (LogarithmicallyIntegrable (fun r => h r / r ^ a) →
        ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A)) := by
  let h₂ : ℝ → ℝ := fun r => (1 - δ₂ r) * h r
  let u : ℝ → ℝ := fun r => h r / r ^ a
  let u₂ : ℝ → ℝ := fun r => h₂ r / r ^ a
  let U : ℝ → ℝ := fun s => h s / s ^ (a + 1)
  let U₂ : ℝ → ℝ := fun s => h₂ s / s ^ (a + 1)
  have hhm₂ : Measurable h₂ := (measurable_const.sub hδ₂m).mul hhm
  have hum : Measurable u := hhm.div (by fun_prop)
  have hum₂ : Measurable u₂ := hhm₂.div (by fun_prop)
  have hfac : Tendsto (fun r => 1 - δ₂ r) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hδ₂0
  have hepos : ∀ᶠ r in atTop, 0 < 1 - δ₂ r :=
    hfac.eventually (eventually_gt_nhds zero_lt_one)
  have hh₂pos : ∀ᶠ r in atTop, 0 < h₂ r := by
    filter_upwards [hepos, hpos] with r he hr
    exact mul_pos he hr
  have hh₂rv : RegularlyVaryingAtTop h₂ a := by
    apply RegularlyVaryingAtTop.of_tendsto_div hhrv
    apply hfac.congr'
    filter_upwards [hhrv.1] with r hr
    dsimp [h₂]
    field_simp [hr]
  have hode₂ : ∀ x, 0 < x → f' x = (1 - δ₁ x) * a * f x / x + h₂ x / x := by
    intro x hx
    rw [hode x hx]
    dsimp [h₂]
    field_simp [hx.ne']
  let D : RVPosData h a := RVPosData.of ha hhm hhrv hpos
  obtain ⟨r₀, hrR, hr₀, hU₂int, hmain, hfinite⟩ :=
    lemma_I_5_6_reduced (R := D.threshold) ha hhm₂ hh₂rv hh₂pos hfpos hderiv hδ₁ hode₂
  have hrD : D.threshold ≤ r₀ := hrR
  have hUpos : ∀ x, r₀ ≤ x → 0 < U x := by
    intro x hx
    exact div_pos (D.pos_above x (hrD.trans hx))
      (Real.rpow_pos_of_pos (hr₀.trans_le hx) (a + 1))
  have hUint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable U volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := D.bddAbove_Icc y
    have hh : IntervalIntegrable h volume x y := by
      apply intervalIntegrable_of_bound hhm.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
      rw [uIcc_of_le hxy] at hs
      rw [Real.norm_eq_abs, abs_of_pos (D.pos_above s ((hrD.trans hx).trans hs.1))]
      exact hC s ((hrD.trans hx).trans hs.1) hs.2
    have hIc : IntegrableOn h (Icc x y) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by finiteness)).1 hh
    have hcont : ContinuousOn (fun s : ℝ => (s ^ (a + 1))⁻¹) (Icc x y) := by
      apply ContinuousOn.inv₀
      · intro s hs
        exact (Real.continuousAt_rpow_const s (a + 1)
          (Or.inl ((hr₀.trans_le (hx.trans hs.1)).ne'))).continuousWithinAt
      · intro s hs
        exact (Real.rpow_pos_of_pos ((hr₀.trans_le hx).trans_le hs.1) (a + 1)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    simpa [U, div_eq_mul_inv] using hIc.mul_continuousOn hcont isCompact_Icc
  have hum₂eq : ∀ r, u₂ r = (1 - δ₂ r) * u r := by
    intro r
    dsimp [u₂, u, h₂]
    ring
  have hforward : LogarithmicallyIntegrable u → LogarithmicallyIntegrable u₂ := by
    intro hu
    have hliminv : Tendsto (fun r => (1 - δ₂ r)⁻¹) atTop (𝓝 1) := by
      simpa using hfac.inv₀ one_ne_zero
    have hlog := logarithmicallyIntegrable_div_of_tendsto_pos one_pos hliminv hu
      ((measurable_const.sub hδ₂m).inv)
    apply hlog.congr_of_eventuallyEq _ hum₂
    filter_upwards with r
    rw [hum₂eq]
    field_simp
  have hback : LogarithmicallyIntegrable u₂ → LogarithmicallyIntegrable u := by
    intro hu₂
    have hlog := logarithmicallyIntegrable_div_of_tendsto_pos one_pos hfac hu₂
      (measurable_const.sub hδ₂m)
    apply hlog.congr_of_eventuallyEq _ hum
    filter_upwards [hepos] with r he
    rw [hum₂eq]
    field_simp [he.ne']
  refine ⟨r₀, hr₀, hUint, ?_, ?_⟩
  · intro hnot
    change ¬ LogarithmicallyIntegrable u at hnot
    change Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, U s)) atTop (𝓝 1)
    have hnot₂ : ¬ LogarithmicallyIntegrable u₂ := fun hu₂ => hnot (hback hu₂)
    have hm := hmain hnot₂
    have hnotU : ¬ IntegrableOn U (Ioi r₀) volume := by
      intro hUi
      apply hnot
      refine ⟨hum, r₀, hr₀, ?_⟩
      apply hUi.congr_fun _ measurableSet_Ioi
      intro s hs
      have hs0 : 0 < s := hr₀.trans hs
      have hsr₀ : r₀ ≤ s := hs.le
      change U s = |u s| / s
      have hupos : 0 < u s := div_pos (D.pos_above s (hrD.trans hsr₀))
        (Real.rpow_pos_of_pos hs0 a)
      have hpow : s ^ (a + 1) = s ^ a * s := by rw [Real.rpow_add hs0, Real.rpow_one]
      dsimp [U, u]
      rw [hpow, abs_of_pos hupos]
      ring
    have hUinf : Tendsto (fun r => ∫ s in r₀..r, U s) atTop atTop :=
      tendsto_intervalIntegral_atTop_of_not_integrableOn (fun x y hx hxy => hUint x y hx hxy)
        (fun x hx => (hUpos x hx).le) hnotU
    have hUratio : Tendsto (fun s => U₂ s / U s) atTop (𝓝 1) := by
      apply hfac.congr'
      filter_upwards [eventually_ge_atTop r₀] with s hs
      have hfactor : U₂ s = (1 - δ₂ s) * U s := by
        dsimp [U₂, U, h₂]
        ring
      rw [hfactor]
      field_simp [(hUpos s hs).ne']
    have hIntRatio := tendsto_intervalIntegral_div_of_tendsto_ratio hUpos hUratio
      (fun x y hx hxy => hU₂int x y hx hxy) (fun x y hx hxy => hUint x y hx hxy) hUinf
    have hmul := hm.mul hIntRatio
    rw [mul_one] at hmul
    apply hmul.congr'
    filter_upwards [hUinf.eventually (eventually_gt_atTop 0),
      hIntRatio.eventually (eventually_gt_nhds zero_lt_one)] with r hrI hrRatio
    have hrI₂ : 0 < ∫ s in r₀..r, U₂ s := (div_pos_iff_of_pos_right hrI).mp hrRatio
    change f r / (r ^ a * ∫ s in r₀..r, U₂ s) * ((∫ s in r₀..r, U₂ s) / (∫ s in r₀..r, U s)) =
      f r / (r ^ a * ∫ s in r₀..r, U s)
    field_simp [hrI.ne', hrI₂.ne']
  · intro hu
    exact hfinite (hforward hu)

/-- **Logarithmic corollary of Lemma I.5.6 with both errors.** If
`h(r) ∼ A r^a`, then `f(r) ∼ A r^a log r`. -/
theorem lemma_I_5_6_log_of_errors {f f' h δ₁ δ₂ : ℝ → ℝ} {a A : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hhm : Measurable h)
    (hhrv : RegularlyVaryingAtTop h a) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂m : Measurable δ₂) (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ x, 0 < x →
      f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x)
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (A * r ^ a * Real.log r)) atTop (𝓝 1) := by
  let u : ℝ → ℝ := fun r => h r / r ^ a
  have huA : Tendsto (fun r => u r / A) atTop (𝓝 1) := by
    apply hhA.congr'
    filter_upwards with r
    dsimp [u]
    ring
  have hulim : Tendsto u atTop (𝓝 A) := by
    have hm := huA.const_mul A
    rw [mul_one] at hm
    apply hm.congr'
    filter_upwards with r
    dsimp [u]
    field_simp [hA.ne']
  have hnot : ¬ LogarithmicallyIntegrable (fun r => h r / r ^ a) := by
    exact not_logarithmicallyIntegrable_of_tendsto_pos hA hulim
  have hhe : ∀ᶠ x in atTop, 0 < h x := hpos
  obtain ⟨r₀, hr₀, hUint, hnon, _⟩ := lemma_I_5_6_of_errors ha hhm hhrv hhe hfpos hderiv hδ₁ hδ₂m hδ₂0 hode
  have hmain := hnon hnot
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
  have hIU : 0 < ∫ s in r₀..r, U s :=
    (div_pos_iff_of_pos_right hden).mp hratio
  change f r / (r ^ a * ∫ s in r₀..r, U s) * ((∫ s in r₀..r, U s) / (A * Real.log r)) =
    f r / (A * r ^ a * Real.log r)
  field_simp [hA.ne', hrlog, hIU.ne', (Real.rpow_pos_of_pos hr0 a).ne']



#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_6_reduced
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_6_log_of_tendsto
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_6_of_errors
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_6_log_of_errors

end PercLib.CriticalLRP.Analysis
