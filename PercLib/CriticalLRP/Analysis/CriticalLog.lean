/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Critical logarithmic integration

Independent normalized increments for the critical driven ODE, the positive
power normalization of its exponential integrating weight, transfers of
logarithmic integrability through asymptotically positive factors, and the
integral comparison used when a positive denominator integral diverges.
-/

module

public import PercLib.CriticalLRP.Analysis.Lemma_I_5_5

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

theorem normalized_increment_of_driving_ode_unweighted {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a r₀ R : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hrD : D.threshold ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hode : ∀ x, r₀ ≤ x → f' x = (1 - δ x) * a * f x / x + h x / x) :
    (f R * (powerExpWeight r₀ a δ R)⁻¹) - (f r₀ * (powerExpWeight r₀ a δ r₀)⁻¹) =
      ∫ s in r₀..R, h s / (s * powerExpWeight r₀ a δ s) := by
  let w := powerExpWeight r₀ a δ
  let H : ℝ → ℝ := fun r => ∫ s in r₀..r, errorTail r₀ δ s / s
  let q : ℝ → ℝ := fun r => f r * (w r)⁻¹
  have hHac : AbsolutelyContinuousOnInterval H r₀ R :=
    (intervalIntegrable_errorTail_div hr₀ hδm hδ1 r₀ R).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc
  obtain ⟨B, hB⟩ := hHac.exists_bound
  have hACexp : ∀ c : ℝ, AbsolutelyContinuousOnInterval (fun x => Real.exp (c * H x)) r₀ R := by
    intro c
    apply absolutelyContinuousOnInterval_exp_of_bound (B := |c| * B) (hHac.const_mul c)
    intro x hx
    have hb := hB x hx
    rw [Real.norm_eq_abs] at hb
    calc |c * H x| = |c| * |H x| := abs_mul _ _
      _ ≤ |c| * B := mul_le_mul_of_nonneg_left hb (abs_nonneg c)
  have hwAC : AbsolutelyContinuousOnInterval w r₀ R := by
    change AbsolutelyContinuousOnInterval (fun x => x ^ a * Real.exp (-(a * H x))) r₀ R
    have hfun : (fun x : ℝ => x ^ a * Real.exp (-(a * H x))) =
        (fun x : ℝ => x ^ a) * (fun x => Real.exp (-(a * H x))) := by rfl
    rw [hfun]
    exact (absolutelyContinuousOnInterval_rpow hr₀ hR (α := a)).mul
      (by simpa only [neg_mul] using hACexp (-a))
  have hwiAC : AbsolutelyContinuousOnInterval
      (fun x => x ^ (-a) * Real.exp (a * H x)) r₀ R :=
    (absolutelyContinuousOnInterval_rpow hr₀ hR (α := -a)).mul (hACexp a)
  have hfc : ContinuousOn f (Icc r₀ R) := by
    intro x hx
    exact (hderiv x hx.1).continuousAt.continuousWithinAt
  obtain ⟨Cf, hCf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Ch, hCh⟩ := D.bddAbove_Icc R
  have hf0 : 0 ≤ Cf := (norm_nonneg (f r₀)).trans (hCf r₀ ⟨le_rfl, hR⟩)
  have hh0 : 0 ≤ Ch := (D.pos_above r₀ hrD).le.trans (hCh r₀ hrD hR)
  have hf'bound : ∀ x ∈ uIcc r₀ R, ‖f' x‖ ≤ 2 * (a * Cf + Ch) / r₀ := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
    have hfx : |f x| ≤ Cf := hCf x hx
    have hhx : |h x| ≤ Ch := by
      rw [abs_of_pos (D.pos_above x (le_trans hrD hx.1))]
      exact hCh x (le_trans hrD hx.1) hx.2
    have hfac : |1 - δ x| ≤ 2 := by
      calc |1 - δ x| ≤ |1| + |δ x| := abs_sub _ _
        _ ≤ 2 := by have hd := hδ1 x hx.1; rw [abs_one]; linarith
    have hfirst : |(1 - δ x) * (a * f x)| ≤ 2 * (a * Cf) := by
      rw [abs_mul, abs_mul, abs_of_pos ha]
      exact mul_le_mul hfac (mul_le_mul_of_nonneg_left hfx ha.le)
        (mul_nonneg ha.le (abs_nonneg _)) (by norm_num)
    have hsum : |(1 - δ x) * a * f x + h x| ≤ 2 * (a * Cf + Ch) := by
      calc |(1 - δ x) * a * f x + h x|
          ≤ |(1 - δ x) * (a * f x)| + |h x| := by
            rw [mul_assoc]
            exact abs_add_le _ _
        _ ≤ 2 * (a * Cf) + Ch := add_le_add hfirst hhx
        _ ≤ 2 * (a * Cf + Ch) := by nlinarith [hh0]
    rw [hode x hx.1, show (1 - δ x) * a * f x / x + h x / x =
      ((1 - δ x) * a * f x + h x) / x by ring, Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    calc |(1 - δ x) * a * f x + h x| / x ≤ 2 * (a * Cf + Ch) / x :=
      div_le_div_of_nonneg_right hsum hx0.le
    _ ≤ 2 * (a * Cf + Ch) / r₀ := by
      have hcross : 2 * (a * Cf + Ch) * r₀ ≤ 2 * (a * Cf + Ch) * x :=
        mul_le_mul_of_nonneg_left hx.1 (by positivity)
      exact (div_le_div_iff₀ hx0 hr₀).2 hcross
  have hfAC : AbsolutelyContinuousOnInterval f r₀ R := by
    apply absolutelyContinuousOnInterval_of_hasDerivAt_bounded (C := 2 * (a * Cf + Ch) / r₀)
    · intro x hx
      rw [uIcc_of_le hR] at hx
      exact hderiv x hx.1
    · exact hf'bound
  have hwi : EqOn (fun x => x ^ (-a) * Real.exp (a * H x))
      (fun x => (w x)⁻¹) (uIcc r₀ R) := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
    change x ^ (-a) * Real.exp (a * H x) =
      (x ^ a * Real.exp (-(a * H x)))⁻¹
    calc x ^ (-a) * Real.exp (a * H x)
        = (x ^ a)⁻¹ * (Real.exp (-(a * H x)))⁻¹ := by
          rw [Real.rpow_neg hx0.le]
          congr 1
          field_simp [Real.exp_ne_zero]
          rw [← Real.exp_add]
          simp
      _ = (x ^ a * Real.exp (-(a * H x)))⁻¹ := by rw [mul_inv_rev]; ring
  have hqAC : AbsolutelyContinuousOnInterval q r₀ R := by
    apply (hfAC.mul hwiAC).congr
    intro x hx
    dsimp [q]
    exact congrArg (fun z => f x * z) (hwi hx)
  have hqderiv : ∀ᵐ x, x ∈ Ioc r₀ R →
      deriv q x = h x / (x * w x) := by
    filter_upwards [ae_hasDerivAt_powerExpWeight ha hr₀ hR hδm hδ1] with x hx
    intro hxmem
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxmem.1.le
    have hwpos : 0 < w x := by
      dsimp [w, powerExpWeight]
      exact mul_pos (Real.rpow_pos_of_pos hxpos a) (Real.exp_pos _)
    have hw := hx hxmem
    have hq := (hderiv x hxmem.1.le).mul (hw.inv hwpos.ne')
    have hqd : deriv q x = f' x * (w x)⁻¹ +
        f x * (-(a * (1 - δ x) * w x / x) / (w x) ^ 2) := hq.deriv
    rw [hqd, hode x hxmem.1.le]
    field_simp [hxpos.ne', hwpos.ne']
    ring
  calc (f R * (powerExpWeight r₀ a δ R)⁻¹) - (f r₀ * (powerExpWeight r₀ a δ r₀)⁻¹)
      = ∫ s in r₀..R, deriv q s := hqAC.integral_deriv_eq_sub.symm
    _ = ∫ s in r₀..R, h s / (s * powerExpWeight r₀ a δ s) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hqderiv] with x hx
        intro hxmem
        exact hx (by rwa [uIoc_of_le hR] at hxmem)



/-- The exponential weight has a positive power-normalized limit when its error
is logarithmically integrable. -/
theorem tendsto_powerExpWeight_div_rpow {δ : ℝ → ℝ} {r₀ a : ℝ} (hr₀ : 0 < r₀)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hδlog : LogarithmicallyIntegrable δ) :
    ∃ A : ℝ, 0 < A ∧
      Tendsto (fun r => powerExpWeight r₀ a δ r / r ^ a) atTop (𝓝 A) := by
  obtain ⟨r₂, hr₂, hint⟩ := hδlog.2
  let d : ℝ → ℝ := fun s => errorTail r₀ δ s / s
  let R : ℝ := max r₀ r₂
  have hRr₀ : r₀ ≤ R := le_max_left _ _
  have hRr₂ : r₂ ≤ R := le_max_right _ _
  have hR0 : 0 < R := hr₀.trans_le hRr₀
  have hdm : Measurable d := (measurable_errorTail hδm).div measurable_id
  have hlocal : IntegrableOn d (Ioc r₀ R) volume:=
    (intervalIntegrable_errorTail_div hr₀ hδm hδ1 r₀ R).1
  have htail : IntegrableOn d (Ioi R) volume := by
    apply (hint.mono_set (Ioi_subset_Ioi hRr₂)).mono' hdm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hR0.trans hs
    have hsr₀ : r₀ < s := hRr₀.trans_lt hs
    simp [d, errorTail, hsr₀, Real.norm_eq_abs, abs_of_pos hs0]
  have hset : Ioc r₀ R ∪ Ioi R = Ioi r₀ := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · exact hRr₀.trans_lt hx
    · intro hx
      by_cases hxR : x ≤ R
      · exact Or.inl ⟨hx, hxR⟩
      · exact Or.inr (lt_of_not_ge hxR)
  have hintd : IntegrableOn d (Ioi r₀) volume := by
    rw [← hset]
    exact hlocal.union htail
  let L : ℝ := ∫ s in Ioi r₀, d s
  have hlimint : Tendsto (fun r => ∫ s in r₀..r, d s) atTop (𝓝 L) :=
    intervalIntegral_tendsto_integral_Ioi r₀ hintd tendsto_id
  have hlimexp : Tendsto (fun r => Real.exp (-(a * ∫ s in r₀..r, d s))) atTop
      (𝓝 (Real.exp (-(a * L)))) := by
    apply Real.continuous_exp.continuousAt.tendsto.comp
    simpa using (hlimint.const_mul a).neg
  refine ⟨Real.exp (-(a * L)), Real.exp_pos _, ?_⟩
  apply hlimexp.congr'
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hr0 : 0 < r := hr₀.trans_le hr
  dsimp [powerExpWeight]
  symm
  change r ^ a * Real.exp (-(a * ∫ s in r₀..r, d s)) / r ^ a =
    Real.exp (-(a * ∫ s in r₀..r, d s))
  field_simp [(Real.rpow_pos_of_pos hr0 a).ne']

/-- Eventual equality preserves logarithmic integrability. -/
theorem LogarithmicallyIntegrable.congr_of_eventuallyEq {u v : ℝ → ℝ}
    (hu : LogarithmicallyIntegrable u) (huv : u =ᶠ[atTop] v) (hvm : Measurable v) :
    LogarithmicallyIntegrable v := by
  obtain ⟨hum, r₀, hr₀, hint⟩ := hu
  obtain ⟨R, hR⟩ := eventually_atTop.1 huv
  refine ⟨hvm, max r₀ R, lt_max_of_lt_left hr₀, ?_⟩
  have hsub : IntegrableOn (fun r => |u r| / r) (Ioi (max r₀ R)) volume :=
    hint.mono_set (Ioi_subset_Ioi (le_max_left _ _))
  apply hsub.congr_fun _ measurableSet_Ioi
  intro r hr
  rw [mem_Ioi] at hr
  change |u r| / r = |v r| / r
  rw [hR r ((le_max_right r₀ R).trans hr.le)]

/-- Division by a function tending to a positive finite limit preserves
logarithmic integrability. -/
theorem logarithmicallyIntegrable_div_of_tendsto_pos {u E : ℝ → ℝ} {A : ℝ}
    (hA : 0 < A) (hlim : Tendsto E atTop (𝓝 A))
    (hu : LogarithmicallyIntegrable u) (hEm : Measurable E) :
    LogarithmicallyIntegrable (fun s => u s / E s) := by
  obtain ⟨hum, r₀, hr₀, hint⟩ := hu
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hlim (A / 2) (by positivity)
  let R : ℝ := max r₀ B
  have hRr₀ : r₀ ≤ R := le_max_left _ _
  have hRB : B ≤ R := le_max_right _ _
  have hR0 : 0 < R := hr₀.trans_le hRr₀
  refine ⟨hum.div hEm, R, hR0, ?_⟩
  have hbase : IntegrableOn (fun s => (2 / A) * (|u s| / s)) (Ioi R) volume :=
    (hint.mono_set (Ioi_subset_Ioi hRr₀)).const_mul (2 / A)
  apply hbase.mono' ((hum.div hEm).abs.div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hR0.trans hs
  have hdist := hB s (hRB.trans hs.le)
  rw [Real.dist_eq, abs_lt] at hdist
  have hElow : A / 2 < E s := by linarith [hdist.1, hdist.2]
  have hEpos : 0 < E s := by linarith
  simp only [Pi.div_apply, id_eq]
  change ‖|u s / E s| / s‖ ≤ (2 / A) * (|u s| / s)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ |u s / E s| / s by positivity),
    abs_div, abs_of_pos hEpos]
  calc |u s| / E s / s = (|u s| / s) / E s := by ring
    _ ≤ (|u s| / s) / (A / 2) := by gcongr
    _ = (2 / A) * (|u s| / s) := by field_simp

/-- A nonnegative locally integrable function with a nonintegrable positive tail
has an interval primitive tending to infinity. -/
theorem tendsto_intervalIntegral_atTop_of_not_integrableOn {u : ℝ → ℝ} {a : ℝ}
    (huint : ∀ x y : ℝ, a ≤ x → x ≤ y → IntervalIntegrable u volume x y)
    (hunonneg : ∀ x, a ≤ x → 0 ≤ u x) (hnot : ¬ IntegrableOn u (Ioi a) volume) :
    Tendsto (fun r => ∫ s in a..r, u s) atTop atTop := by
  classical
  let G : ℝ → ℝ := fun r => ∫ s in a..r, u s
  by_cases hunbounded : ∀ M : ℝ, ∃ b, a ≤ b ∧ M ≤ G b
  · refine tendsto_atTop.2 fun M => ?_
    obtain ⟨b, hab, hMb⟩ := hunbounded M
    filter_upwards [eventually_ge_atTop b] with r hbr
    have har : a ≤ r := hab.trans hbr
    have hInt : 0 ≤ ∫ s in b..r, u s := by
      apply intervalIntegral.integral_nonneg hbr
      intro s hs
      exact hunonneg s (hab.trans hs.1)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (huint a b le_rfl hab) (huint b r hab hbr)
    change M ≤ G r
    dsimp [G] at hMb ⊢
    linarith
  · push Not at hunbounded
    obtain ⟨M, hM⟩ := hunbounded
    exfalso
    apply hnot
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded M a (b := fun r : ℝ => r)
      (f := u) (fun b => ?_) tendsto_id ?_
    · by_cases hab : a ≤ b
      · exact (huint a b le_rfl hab).1
      · have hba : b < a := lt_of_not_ge hab
        rw [Set.Ioc_eq_empty (not_lt_of_ge hba.le)]
        exact integrableOn_empty
    · filter_upwards [eventually_ge_atTop a] with b hab
      have hnorm : (∫ s in a..b, ‖u s‖) = ∫ s in a..b, u s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hab] at hs
        change ‖u s‖ = u s
        rw [Real.norm_eq_abs, abs_of_nonneg (hunonneg s hs.1)]
      change (∫ s in a..b, ‖u s‖) ≤ M
      rw [hnorm]
      exact (hM b hab).le

/-- Integrals of asymptotically proportional functions are asymptotically
proportional when the positive denominator integral diverges. -/
theorem tendsto_intervalIntegral_div_of_tendsto_ratio {F G : ℝ → ℝ} {a C : ℝ}
    (hGpos : ∀ x, a ≤ x → 0 < G x)
    (hFG : Tendsto (fun x => F x / G x) atTop (𝓝 C))
    (hFint : ∀ x y : ℝ, a ≤ x → x ≤ y → IntervalIntegrable F volume x y)
    (hGint : ∀ x y : ℝ, a ≤ x → x ≤ y → IntervalIntegrable G volume x y)
    (hGinf : Tendsto (fun r => ∫ s in a..r, G s) atTop atTop) :
    Tendsto (fun r => (∫ s in a..r, F s) / (∫ s in a..r, G s)) atTop (𝓝 C) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.1 hFG η hη
  let R : ℝ := max a R₀
  have haR : a ≤ R := le_max_left _ _
  have hR₀R : R₀ ≤ R := le_max_right _ _
  let B : ℝ := (∫ s in a..R, F s) - C * (∫ s in a..R, G s)
  have hB0 : Tendsto (fun r => |B| / (∫ s in a..r, G s)) atTop (𝓝 0) := by
    have hi := hGinf.inv_tendsto_atTop.const_mul |B|
    simpa [div_eq_mul_inv] using hi
  obtain ⟨R₁, hR₁⟩ := Metric.tendsto_atTop.1 hB0 η hη
  obtain ⟨R₂, hR₂⟩ := eventually_atTop.1
    (hGinf.eventually (eventually_gt_atTop 0))
  refine ⟨max R (max R₁ R₂), fun r hr => ?_⟩
  have hrR : R ≤ r := (le_max_left _ _).trans hr
  have hrR₁ : R₁ ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hr
  have hrpos : 0 < ∫ s in a..r, G s :=
    hR₂ r (((le_max_right _ _).trans (le_max_right _ _)).trans hr)
  have hRr : R ≤ r := hrR
  have hFadd := intervalIntegral.integral_add_adjacent_intervals
    (hFint a R le_rfl haR) (hFint R r haR hRr)
  have hGadd := intervalIntegral.integral_add_adjacent_intervals
    (hGint a R le_rfl haR) (hGint R r haR hRr)
  have hden : ((∫ s in a..R, G s) + (∫ s in R..r, G s)) ≠ 0 := by
    rw [hGadd]
    exact hrpos.ne'
  have hratio : (∫ s in a..r, F s) / (∫ s in a..r, G s) - C =
      (((∫ s in R..r, F s) - C * (∫ s in R..r, G s)) + B) /
        (∫ s in a..r, G s) := by
    rw [← hFadd, ← hGadd]
    dsimp [B]
    field_simp [hden]
    ring
  rw [Real.dist_eq, hratio]
  have htail : |(∫ s in R..r, F s) - C * (∫ s in R..r, G s)| ≤
      η * (∫ s in R..r, G s) := by
    have hNint : IntervalIntegrable (fun s => F s - C * G s) volume R r :=
      (hFint R r haR hRr).sub ((hGint R r haR hRr).const_mul C)
    have hηGint : IntervalIntegrable (fun s => η * G s) volume R r :=
      (hGint R r haR hRr).const_mul η
    have hpoint : ∀ s ∈ Icc R r, |F s - C * G s| ≤ η * G s := by
      intro s hs
      have hsR₀ : R₀ ≤ s := hR₀R.trans hs.1
      have hsA : a ≤ s := haR.trans hs.1
      have hsG := hGpos s hsA
      have hd := hR₀ s hsR₀
      rw [Real.dist_eq, abs_lt] at hd
      have habs : |F s / G s - C| < η := abs_lt.2 hd
      have heq : F s / G s - C = (F s - C * G s) / G s := by
        field_simp [hsG.ne']
      rw [heq, abs_div, abs_of_pos hsG] at habs
      exact ((div_lt_iff₀ hsG).1 habs).le
    calc |(∫ s in R..r, F s) - C * (∫ s in R..r, G s)| =
        |∫ s in R..r, (F s - C * G s)| := by
          have hsub := intervalIntegral.integral_sub (hFint R r haR hRr)
            ((hGint R r haR hRr).const_mul C)
          rw [intervalIntegral.integral_const_mul] at hsub
          exact congrArg abs hsub.symm
      _ ≤ ∫ s in R..r, |F s - C * G s| :=
        intervalIntegral.abs_integral_le_integral_abs hRr
      _ ≤ ∫ s in R..r, η * G s :=
        intervalIntegral.integral_mono_on hRr hNint.norm hηGint hpoint
      _ = η * (∫ s in R..r, G s) := intervalIntegral.integral_const_mul _ _
  have htailGnonneg : 0 ≤ ∫ s in R..r, G s := by
    apply intervalIntegral.integral_nonneg hRr
    intro s hs
    exact (hGpos s (haR.trans hs.1)).le
  have hbaseGnonneg : 0 ≤ ∫ s in a..R, G s := by
    apply intervalIntegral.integral_nonneg haR
    intro s hs
    exact (hGpos s hs.1).le
  have htail_le : (∫ s in R..r, G s) ≤ ∫ s in a..r, G s := by
    rw [← hGadd]
    linarith
  have hfrac : (∫ s in R..r, G s) / (∫ s in a..r, G s) ≤ 1 := by
    apply (div_le_iff₀ hrpos).2
    simpa using htail_le
  have hηfrac : η * (∫ s in R..r, G s) / (∫ s in a..r, G s) ≤ η := by
    calc η * (∫ s in R..r, G s) / (∫ s in a..r, G s) =
        η * ((∫ s in R..r, G s) / (∫ s in a..r, G s)) := by ring
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left hfrac hη.le
      _ = η := mul_one η
  have hB := hR₁ r hrR₁
  rw [Real.dist_eq, sub_zero] at hB
  have hfirst : |(∫ s in R..r, F s) - C * (∫ s in R..r, G s)| /
      (∫ s in a..r, G s) ≤ η * (∫ s in R..r, G s) / (∫ s in a..r, G s) := by
    exact div_le_div_of_nonneg_right htail hrpos.le
  rw [abs_div, abs_of_pos hrpos]
  calc |((∫ s in R..r, F s) - C * (∫ s in R..r, G s)) + B| /
        (∫ s in a..r, G s)
      ≤ (|(∫ s in R..r, F s) - C * (∫ s in R..r, G s)| + |B|) /
        (∫ s in a..r, G s) := by
          exact div_le_div_of_nonneg_right (abs_add_le _ _) hrpos.le
    _ = |(∫ s in R..r, F s) - C * (∫ s in R..r, G s)| /
          (∫ s in a..r, G s) + |B| / (∫ s in a..r, G s) := by ring
    _ ≤ η * (∫ s in R..r, G s) / (∫ s in a..r, G s) +
          |B| / (∫ s in a..r, G s) := add_le_add hfirst (le_refl _)
    _ ≤ η + |B| / (∫ s in a..r, G s) := add_le_add hηfrac (le_refl _)
    _ < ε := by
        have habs_nonneg : 0 ≤ |B| / (∫ s in a..r, G s) := by positivity
        rw [abs_of_nonneg habs_nonneg] at hB
        dsimp [η] at hB ⊢
        linarith

/-- On a positive locally integrable tail, logarithmic integrability of `v`
is precisely tail integrability of `v / r`. -/
theorem integrableOn_div_of_logarithmicallyIntegrable {v : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hvpos : ∀ x, r₀ ≤ x → 0 < v x)
    (hvint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => v s / s) volume x y)
    (hvlog : LogarithmicallyIntegrable v) :
    IntegrableOn (fun s => v s / s) (Ioi r₀) volume := by
  obtain ⟨r₂, hr₂, hint⟩ := hvlog.2
  let R : ℝ := max r₀ r₂
  have hRr₀ : r₀ ≤ R := le_max_left _ _
  have hRr₂ : r₂ ≤ R := le_max_right _ _
  have hR0 : 0 < R := hr₀.trans_le hRr₀
  have hlocal : IntegrableOn (fun s => v s / s) (Ioc r₀ R) volume :=
    (hvint r₀ R le_rfl hRr₀).1
  have htail : IntegrableOn (fun s => v s / s) (Ioi R) volume := by
    apply (hint.mono_set (Ioi_subset_Ioi hRr₂)).congr_fun _ measurableSet_Ioi
    intro s hs
    have hs0 : 0 < s := hR0.trans hs
    have hvs : 0 < v s := hvpos s (hRr₀.trans hs.le)
    change |v s| / s = v s / s
    rw [abs_of_pos hvs]
  have hset : Ioc r₀ R ∪ Ioi R = Ioi r₀ := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · exact hRr₀.trans_lt hx
    · intro hx
      by_cases hxR : x ≤ R
      · exact Or.inl ⟨hx, hxR⟩
      · exact Or.inr (lt_of_not_ge hxR)
  rw [← hset]
  exact hlocal.union htail

/-- A measurable function with a positive finite limit is not logarithmically
integrable. -/
theorem not_logarithmicallyIntegrable_of_tendsto_pos {u : ℝ → ℝ} {A : ℝ}
    (hA : 0 < A) (hulim : Tendsto u atTop (𝓝 A)) :
    ¬ LogarithmicallyIntegrable u := by
  intro hulog
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hulim (A / 2) (by positivity)
  obtain ⟨r₀, hr₀, hint⟩ := hulog.2
  let R : ℝ := max r₀ B
  have hRr₀ : r₀ ≤ R := le_max_left _ _
  have hRB : B ≤ R := le_max_right _ _
  have hR0 : 0 < R := hr₀.trans_le hRr₀
  have hsub := hint.mono_set (Ioi_subset_Ioi hRr₀)
  have hscaled : IntegrableOn (fun x : ℝ => (A / 2) * x⁻¹) (Ioi R) volume := by
    apply hsub.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hR0.trans hx
    have hd := hB x (hRB.trans hx.le)
    rw [Real.dist_eq, abs_lt] at hd
    have huA : A / 2 < u x := by linarith [hd.1, hd.2]
    have habs : A / 2 < |u x| := huA.trans_le (le_abs_self _)
    change ‖(A / 2) * x⁻¹‖ ≤ |u x| / x
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (A / 2) * x⁻¹)]
    calc (A / 2) * x⁻¹ = (A / 2) / x := by ring
      _ ≤ |u x| / x := (div_le_div_iff_of_pos_right hx0).2 habs.le
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi R) volume := by
    have hc : IntegrableOn (fun x : ℝ => (A / 2)⁻¹ * ((A / 2) * x⁻¹)) (Ioi R) volume :=
      hscaled.const_mul (A / 2)⁻¹
    apply IntegrableOn.congr_fun hc _ measurableSet_Ioi
    intro x hx
    change (A / 2)⁻¹ * ((A / 2) * x⁻¹) = x⁻¹
    field_simp [ne_of_gt (by positivity : 0 < A / 2)]
  exact not_integrableOn_Ioi_inv hinv

/-- The normalized logarithmic average associated with a positive limit. -/
theorem tendsto_intervalIntegral_div_mul_log {U : ℝ → ℝ} {A r₀ : ℝ}
    (hr₀ : 0 < r₀) (hA : 0 < A)
    (hUA : Tendsto (fun s => U s / (A / s)) atTop (𝓝 1))
    (hUint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable U volume x y) :
    Tendsto (fun r => (∫ s in r₀..r, U s) / (A * Real.log r)) atTop (𝓝 1) := by
  let G : ℝ → ℝ := fun s => A / s
  have hGpos : ∀ x, r₀ ≤ x → 0 < G x := by
    intro x hx
    exact div_pos hA (hr₀.trans_le hx)
  have hGint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable G volume x y := by
    intro x y hx hxy
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hxy]
    intro s hs
    exact (ContinuousAt.div continuousAt_const continuousAt_id
      (hr₀.trans_le (hx.trans hs.1)).ne').continuousWithinAt
  have hEval : ∀ r, r₀ ≤ r → (∫ s in r₀..r, G s) = A * Real.log (r / r₀) := by
    intro r hr
    dsimp [G]
    rw [show (fun s => A / s) = (fun s => A * (1 / s)) by funext s; rw [mul_one_div],
      intervalIntegral.integral_const_mul, integral_one_div_of_pos hr₀ (hr₀.trans_le hr)]
  have hscale : Tendsto (fun r : ℝ => r / r₀) atTop atTop := by
    have hs := (tendsto_const_mul_atTop_of_pos (inv_pos.mpr hr₀)).2 tendsto_id
    apply hs.congr'
    filter_upwards with r
    simp only [id_eq, div_eq_mul_inv]
    ring
  have hlogdiv : Tendsto (fun r => Real.log (r / r₀)) atTop atTop :=
    Real.tendsto_log_atTop.comp hscale
  have hGinf : Tendsto (fun r => ∫ s in r₀..r, G s) atTop atTop := by
    have hl := (tendsto_const_mul_atTop_of_pos hA).2 hlogdiv
    apply hl.congr'
    filter_upwards [eventually_ge_atTop r₀] with r hr
    exact (hEval r hr).symm
  have hratio := tendsto_intervalIntegral_div_of_tendsto_ratio hGpos hUA hUint hGint hGinf
  have hnorm : Tendsto (fun r => (∫ s in r₀..r, U s) /
      (A * Real.log (r / r₀))) atTop (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [eventually_ge_atTop r₀] with r hr
    rw [hEval r hr]
  have hzero : Tendsto (fun r => Real.log r₀ / Real.log r) atTop (𝓝 0) := by
    have hi := Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (Real.log r₀)
    simpa [div_eq_mul_inv] using hi
  have hlogratio : Tendsto (fun r => Real.log (r / r₀) / Real.log r) atTop (𝓝 1) := by
    have hone := (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
    rw [sub_zero] at hone
    apply hone.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr1
    have hr0r : 0 < r := zero_lt_one.trans hr1
    have hrlog : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr1)
    rw [Real.log_div hr0r.ne' hr₀.ne']
    field_simp [hrlog]
  have hmul := hnorm.mul hlogratio
  rw [mul_one] at hmul
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (max r₀ 1)] with r hr
  have hrr₀ : r₀ < r := (le_max_left _ _).trans_lt hr
  have hr1 : 1 < r := (le_max_right _ _).trans_lt hr
  have hr0 : 0 < r := hr₀.trans hrr₀
  have hdiff : Real.log (r / r₀) ≠ 0 := by
    rw [Real.log_div hr0.ne' hr₀.ne']
    exact ne_of_gt (sub_pos.mpr (Real.log_lt_log hr₀ hrr₀))
  have hrlog : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr1)
  field_simp [hA.ne', hdiff, hrlog]


#print axioms PercLib.CriticalLRP.Analysis.normalized_increment_of_driving_ode_unweighted

#print axioms PercLib.CriticalLRP.Analysis.tendsto_powerExpWeight_div_rpow

#print axioms PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable.congr_of_eventuallyEq

#print axioms PercLib.CriticalLRP.Analysis.logarithmicallyIntegrable_div_of_tendsto_pos

#print axioms PercLib.CriticalLRP.Analysis.tendsto_intervalIntegral_atTop_of_not_integrableOn

#print axioms PercLib.CriticalLRP.Analysis.tendsto_intervalIntegral_div_of_tendsto_ratio

#print axioms PercLib.CriticalLRP.Analysis.integrableOn_div_of_logarithmicallyIntegrable

#print axioms PercLib.CriticalLRP.Analysis.not_logarithmicallyIntegrable_of_tendsto_pos

#print axioms PercLib.CriticalLRP.Analysis.tendsto_intervalIntegral_div_mul_log

end PercLib.CriticalLRP.Analysis
