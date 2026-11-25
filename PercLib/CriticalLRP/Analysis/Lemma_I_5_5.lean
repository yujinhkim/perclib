/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.5.5: the driven ODE with a general-order source

The critical case `a = b` is proved without a logarithmic Cesàro hypothesis.
For the exact integrating weight `w`, put `v = h / w` and `q = f / w`.  Then `v`
is slowly varying and `q` has primitive `(1 - δ) * v / r`.  Uniform ratios on
fixed multiplicative windows show `q / v → ∞` and that multiplicative increments
of `q` are negligible relative to `q`.  Consequently `v / q → 0` and `q` is
slowly varying, whether or not the logarithmic primitive converges.

The public theorem `lemma_I_5_5` combines this with the completed `b < a` and
`a < b` cases.  It has the paper's positive, measurable, regularly varying
source `h`, positive differentiable `f`, and derivative-ratio premise.  It
proves regular variation of index `max a b`, together with `h / f → 0` and the
homogeneous derivative asymptotic when `b ≤ a`.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_5_5_lt

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

/-- Uniform ratio bounds on a fixed multiplicative interval to the right. -/
theorem eventually_slowlyVarying_right_le_two {v : ℝ → ℝ} (hvm : Measurable v)
    (hvrv : RegularlyVaryingAtTop v 0) (hvpos : ∀ᶠ x in atTop, 0 < v x)
    {K : ℝ} (hK : 1 < K) :
    ∀ᶠ r in atTop, 0 < v r ∧ ∀ s, r ≤ s → s ≤ K * r → v s ≤ 2 * v r := by
  obtain ⟨X, hX1, hX⟩ := hasLocalUniformRatio_of_regularlyVarying hvm hvrv hvpos
    (K - 1) (by linarith) (1 / 2) (by norm_num)
  obtain ⟨Y, hY⟩ := eventually_atTop.1 hvpos
  filter_upwards [eventually_ge_atTop (max X Y)] with r hr
  have hrX : X ≤ r := le_trans (le_max_left _ _) hr
  have hrY : Y ≤ r := le_trans (le_max_right _ _) hr
  have hr1 : 1 ≤ r := le_trans hX1 hrX
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  refine ⟨hY r hrY, fun s hrs hsr => ?_⟩
  have hl : s / r ∈ Icc (1 : ℝ) (1 + (K - 1)) := by
    constructor
    · exact (le_div_iff₀ hr0).2 (by simpa using hrs)
    · have hle : s / r ≤ K := (div_le_iff₀ hr0).2 (by simpa [mul_comm] using hsr)
      simpa using hle
  have hu := hX r hrX (s / r) hl
  rw [div_mul_cancel₀ s hr0.ne'] at hu
  simp only [Real.rpow_zero] at hu
  have hratio : v s / v r ≤ 3 / 2 := by
    have hle := (abs_le.1 hu).2
    norm_num at hle ⊢
    linarith
  have hmul := (div_le_iff₀ (hY r hrY)).1 hratio
  nlinarith [hY r hrY]

/-- Uniform ratio bounds on a fixed multiplicative interval to the left. -/
theorem eventually_half_le_slowlyVarying_left {v : ℝ → ℝ} (hvm : Measurable v)
    (hvrv : RegularlyVaryingAtTop v 0) (hvpos : ∀ᶠ x in atTop, 0 < v x)
    {K : ℝ} (hK : 1 < K) :
    ∀ᶠ r in atTop, 0 < v r ∧ ∀ s, r / K ≤ s → s ≤ r → (1 / 2) * v r ≤ v s := by
  obtain ⟨X, hX1, hX⟩ := hasLocalUniformRatio_of_regularlyVarying hvm hvrv hvpos
    (K - 1) (by linarith) (1 / 2) (by norm_num)
  obtain ⟨Y, hY⟩ := eventually_atTop.1 hvpos
  have hK0 : 0 < K := lt_trans zero_lt_one hK
  filter_upwards [eventually_ge_atTop (K * max X Y)] with r hr
  have hKr : max X Y ≤ r / K := by
    apply (le_div_iff₀ hK0).2
    simpa [mul_comm] using hr
  have hrY : Y ≤ r := by
    have hYK : Y ≤ K * max X Y := by
      have hmax0 : 0 ≤ max X Y := le_trans (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans hX1 (le_max_left _ _))
      nlinarith [le_max_right X Y, mul_le_mul_of_nonneg_left hK.le hmax0]
    exact hYK.trans hr
  refine ⟨hY r hrY, fun s hsr hrs => ?_⟩
  have hsX : X ≤ s := (le_max_left _ _).trans (hKr.trans hsr)
  have hsY : Y ≤ s := (le_max_right _ _).trans (hKr.trans hsr)
  have hs1 : 1 ≤ s := hX1.trans hsX
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  have hvs : 0 < v s := hY s hsY
  have hl : r / s ∈ Icc (1 : ℝ) (1 + (K - 1)) := by
    constructor
    · exact (le_div_iff₀ hs0).2 (by simpa using hrs)
    · have hle : r / s ≤ K := by
        apply (div_le_iff₀ hs0).2
        have hlow := (div_le_iff₀ hK0).1 hsr
        nlinarith
      simpa using hle
  have hu := hX s hsX (r / s) hl
  rw [div_mul_cancel₀ r hs0.ne'] at hu
  simp only [Real.rpow_zero] at hu
  have hratio : v r / v s ≤ 3 / 2 := by
    have hle := (abs_le.1 hu).2
    norm_num at hle ⊢
    linarith
  have hmul := (div_le_iff₀ hvs).1 hratio
  nlinarith

/-- The fixed-window lower bound for a critical logarithmic primitive. -/
theorem eventually_critical_window_lower {v q F δ : ℝ → ℝ} {r₀ K : ℝ}
    (hr₀ : 0 < r₀) (hK : 1 < K) (hvm : Measurable v)
    (hvrv : RegularlyVaryingAtTop v 0) (hvpos : ∀ x, r₀ ≤ x → 0 < v x)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hF : ∀ x, r₀ ≤ x → F x = (1 - δ x) * (v x / x))
    (hFint : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → IntervalIntegrable F volume x y)
    (hq₀ : 0 < q r₀)
    (hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, F s) :
    ∀ᶠ r in atTop, (Real.log K / 4) * v r ≤ q r := by
  have hK0 : 0 < K := zero_lt_one.trans hK
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hδ0 (1 / 2) (by norm_num)
  have hvleft := eventually_half_le_slowlyVarying_left hvm hvrv
    (eventually_atTop.2 ⟨r₀, hvpos⟩) hK
  filter_upwards [hvleft, eventually_ge_atTop (K * max r₀ B)] with r hrv hrB
  have hMr : max r₀ B ≤ r / K := (le_div_iff₀ hK0).2 (by simpa [mul_comm] using hrB)
  have har₀ : r₀ ≤ r / K := (le_max_left _ _).trans hMr
  have haB : B ≤ r / K := (le_max_right _ _).trans hMr
  have ha0 : 0 < r / K := hr₀.trans_le har₀
  have hKr : r / K ≤ r := by
    have hr0 : 0 < r := by
      have hKr₀ : K * r₀ ≤ r :=
        (mul_le_mul_of_nonneg_left (le_max_left r₀ B) hK0.le).trans hrB
      have hfactor : r₀ ≤ K * r₀ := by nlinarith
      exact hr₀.trans_le (hfactor.trans hKr₀)
    apply (div_le_iff₀ hK0).2
    nlinarith
  have hrr₀ : r₀ ≤ r := har₀.trans hKr
  have hr0 : 0 < r := hr₀.trans_le hrr₀
  have hra : r / (r / K) = K := by field_simp
  have hnonneg : 0 ≤ ∫ s in r₀..(r / K), F s := by
    apply intervalIntegral.integral_nonneg har₀
    intro s hs
    have hsr₀ : r₀ ≤ s := hs.1
    rw [hF s hsr₀]
    have hspos : 0 < s := hr₀.trans_le hsr₀
    have hd : 0 ≤ 1 - δ s := by have := (abs_le.1 (hδ1 s hsr₀)).2; linarith
    exact mul_nonneg hd (div_nonneg (hvpos s hsr₀).le hspos.le)
  have hpoint : ∀ s ∈ Icc (r / K) r,
      (v r / 4) / s ≤ F s := by
    intro s hs
    have hsr₀ : r₀ ≤ s := har₀.trans hs.1
    have hs0 : 0 < s := hr₀.trans_le hsr₀
    have hd : (1 : ℝ) / 2 ≤ 1 - δ s := by
      have hdist := hB s (haB.trans hs.1)
      rw [Real.dist_eq, sub_zero, abs_lt] at hdist
      linarith [hdist.1, hdist.2]
    have hprod : (1 / 2) * v s ≤ (1 - δ s) * v s :=
      mul_le_mul_of_nonneg_right hd (hvpos s hsr₀).le
    have hvs := hrv.2 s hs.1 hs.2
    rw [hF s hsr₀]
    calc (v r / 4) / s = ((1 / 2) * ((1 / 2) * v r)) / s := by ring
      _ ≤ ((1 - δ s) * v s) / s := by
        apply (div_le_div_iff_of_pos_right hs0).2
        nlinarith
      _ = (1 - δ s) * (v s / s) := by ring
  have hconstint : IntervalIntegrable (fun s => (v r / 4) / s) volume (r / K) r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hKr]
    intro s hs
    exact (ContinuousAt.div continuousAt_const continuousAt_id
      (hr₀.trans_le (har₀.trans hs.1)).ne').continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on hKr hconstint
    (hFint (r / K) r har₀ hrr₀) hpoint
  have hconstval : (∫ s in (r / K)..r, (v r / 4) / s) =
      (v r / 4) * Real.log K := by
    rw [show (fun s => (v r / 4) / s) = (fun s => (v r / 4) * (1 / s)) by
      funext s; rw [mul_one_div], intervalIntegral.integral_const_mul,
      integral_one_div_of_pos ha0 hr0, hra]
  rw [hconstval] at hmono
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hFint r₀ (r / K) le_rfl har₀) (hFint (r / K) r har₀ hrr₀)
  have hq := hqinc r hrr₀
  have hlower : (∫ s in (r / K)..r, F s) ≤ q r := by
    rw [← hadd] at hq
    have hqv : q r = q r₀ + (∫ s in r₀..(r / K), F s) + ∫ s in (r / K)..r, F s := by
      linarith
    rw [hqv]
    linarith
  have hvposr := hrv.1
  nlinarith

/-- A critical logarithmic primitive grows faster than its slowly varying driver. -/
theorem tendsto_critical_ratio_atTop {v q F δ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hvm : Measurable v)
    (hvrv : RegularlyVaryingAtTop v 0) (hvpos : ∀ x, r₀ ≤ x → 0 < v x)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hF : ∀ x, r₀ ≤ x → F x = (1 - δ x) * (v x / x))
    (hFint : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → IntervalIntegrable F volume x y)
    (hq₀ : 0 < q r₀)
    (hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, F s) :
    Tendsto (fun r => q r / v r) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  let K : ℝ := Real.exp (4 * (|M| + 1))
  have hK : 1 < K := by
    dsimp [K]
    exact Real.one_lt_exp_iff.2 (by positivity)
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hlog : Real.log K / 4 = |M| + 1 := by
    dsimp [K]
    rw [Real.log_exp]
    ring
  have hvpos' : ∀ x, r₀ ≤ x → 0 < v x := hvpos
  have hev := eventually_critical_window_lower hr₀ hK hvm hvrv hvpos hδ0 hδ1
    hF hFint hq₀ hqinc
  filter_upwards [hev, eventually_ge_atTop r₀] with r hr hrr₀
  have hvr := hvpos' r hrr₀
  have hle : (Real.log K / 4) * v r ≤ q r := hr
  rw [hlog] at hle
  have hratio : |M| + 1 ≤ q r / v r := by
    apply (le_div_iff₀ hvr).2
    simpa [mul_comm] using hle
  have hself : M ≤ |M| := le_abs_self M
  linarith

/-- Critical normalized primitives are slowly varying and dominate their drivers. -/
theorem critical_primitive_properties {v q F δ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hvm : Measurable v)
    (hvrv : RegularlyVaryingAtTop v 0) (hvpos : ∀ x, r₀ ≤ x → 0 < v x)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hF : ∀ x, r₀ ≤ x → F x = (1 - δ x) * (v x / x))
    (hFint : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → IntervalIntegrable F volume x y)
    (hq₀ : 0 < q r₀)
    (hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, F s) :
    Tendsto (fun r => q r / v r) atTop atTop ∧
      Tendsto (fun r => v r / q r) atTop (𝓝 0) ∧ RegularlyVaryingAtTop q 0 := by
  have hqv : Tendsto (fun r => q r / v r) atTop atTop :=
    tendsto_critical_ratio_atTop hr₀ hvm hvrv hvpos hδ0 hδ1 hF hFint hq₀ hqinc
  have hqinc' : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y →
      q y - q x = ∫ s in x..y, F s := by
    intro x y hx hy
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hFint r₀ x le_rfl hx) (hFint x y hx hy)
    have hxq := hqinc x hx
    have hyq := hqinc y hy
    linarith
  have hqpos : ∀ x, r₀ ≤ x → 0 < q x := by
    intro x hx
    have hInt : 0 ≤ ∫ s in r₀..x, F s := by
      apply intervalIntegral.integral_nonneg hx
      intro s hs
      have hsr₀ : r₀ ≤ s := hs.1
      have hs0 : 0 < s := hr₀.trans_le hsr₀
      rw [hF s hsr₀]
      have hd : 0 ≤ 1 - δ s := by have := (abs_le.1 (hδ1 s hsr₀)).2; linarith
      exact mul_nonneg hd (div_nonneg (hvpos s hsr₀).le hs0.le)
    have hq := hqinc x hx
    nlinarith
  have hvq : Tendsto (fun r => v r / q r) atTop (𝓝 0) := by
    apply hqv.inv_tendsto_atTop.congr'
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hvr := (hvpos r hr).ne'
    have hqr := (hqpos r hr).ne'
    change (q r / v r)⁻¹ = v r / q r
    field_simp
  refine ⟨hqv, hvq, ?_⟩
  have hbase : ∀ l : ℝ, 1 ≤ l →
      Tendsto (fun r => q (l * r) / q r) atTop (𝓝 1) := by
    intro l hl
    by_cases hl1 : l = 1
    · subst l
      simp only [one_mul]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop r₀] with r hr
      exact (div_self (hqpos r hr).ne').symm
    have hll : 1 < l := lt_of_le_of_ne hl (Ne.symm hl1)
    have hl0 : 0 < l := zero_lt_one.trans hll
    have hvright := eventually_slowlyVarying_right_le_two hvm hvrv
      (eventually_atTop.2 ⟨r₀, hvpos⟩) hll
    have hnonneg : ∀ᶠ r in atTop, 0 ≤ (q (l * r) - q r) / q r := by
      filter_upwards [eventually_ge_atTop r₀] with r hr
      have hl0r : r₀ ≤ l * r := by
        have hr0 : 0 < r := hr₀.trans_le hr
        nlinarith
      have hqr := hqpos r hr
      apply div_nonneg _ hqr.le
      rw [hqinc' r (l * r) hr hl0r]
      apply intervalIntegral.integral_nonneg (by
        have hr0 : 0 < r := hr₀.trans_le hr
        nlinarith)
      intro s hs
      have hsr₀ : r₀ ≤ s := hr.trans hs.1
      have hs0 : 0 < s := hr₀.trans_le hsr₀
      rw [hF s hsr₀]
      have hd : 0 ≤ 1 - δ s := by have := (abs_le.1 (hδ1 s hsr₀)).2; linarith
      exact mul_nonneg hd (div_nonneg (hvpos s hsr₀).le hs0.le)
    have hupper : ∀ᶠ r in atTop,
        (q (l * r) - q r) / q r ≤ (4 * Real.log l) * (v r / q r) := by
      filter_upwards [hvright, eventually_ge_atTop r₀] with r hrv hr
      have hr0 : 0 < r := hr₀.trans_le hr
      have hlr0 : 0 < l * r := mul_pos hl0 hr0
      have hlr : r ≤ l * r := by nlinarith
      have hlrr₀ : r₀ ≤ l * r := hr.trans hlr
      have hpoint : ∀ s ∈ Icc r (l * r), F s ≤ (4 * v r) / s := by
        intro s hs
        have hsr₀ : r₀ ≤ s := hr.trans hs.1
        have hs0 : 0 < s := hr₀.trans_le hsr₀
        have hd : 1 - δ s ≤ 2 := by have := (abs_le.1 (hδ1 s hsr₀)).1; linarith
        have hprod : (1 - δ s) * v s ≤ 2 * (2 * v r) :=
          mul_le_mul hd (hrv.2 s hs.1 hs.2) (hvpos s hsr₀).le (by norm_num)
        rw [hF s hsr₀]
        calc (1 - δ s) * (v s / s) = ((1 - δ s) * v s) / s := by ring
          _ ≤ (2 * (2 * v r)) / s := (div_le_div_iff_of_pos_right hs0).2 hprod
          _ = (4 * v r) / s := by ring
      have hconstint : IntervalIntegrable (fun s => (4 * v r) / s) volume r (l * r) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hlr]
        intro s hs
        exact (ContinuousAt.div continuousAt_const continuousAt_id
          (hr₀.trans_le (hr.trans hs.1)).ne').continuousWithinAt
      have hmono := intervalIntegral.integral_mono_on hlr (hFint r (l * r) hr hlrr₀)
        hconstint hpoint
      have hconstval : (∫ s in r..(l * r), (4 * v r) / s) =
          (4 * v r) * Real.log l := by
        rw [show (fun s => (4 * v r) / s) = (fun s => (4 * v r) * (1 / s)) by
          funext s; rw [mul_one_div], intervalIntegral.integral_const_mul,
          integral_one_div_of_pos hr0 hlr0, mul_div_cancel_right₀ l hr0.ne']
      rw [hconstval] at hmono
      have hdq : q (l * r) - q r ≤ (4 * v r) * Real.log l := by
        rw [hqinc' r (l * r) hr hlrr₀]
        exact hmono
      apply (div_le_iff₀ (hqpos r hr)).2
      calc q (l * r) - q r ≤ (4 * v r) * Real.log l := hdq
        _ = (4 * Real.log l) * (v r / q r) * q r := by
          field_simp [(hqpos r hr).ne']
    have hzero : Tendsto (fun r => (4 * Real.log l) * (v r / q r)) atTop (𝓝 0) := by
      simpa using hvq.const_mul (4 * Real.log l)
    have hdiff : Tendsto (fun r => (q (l * r) - q r) / q r) atTop (𝓝 0) :=
      squeeze_zero' hnonneg hupper hzero
    have hone : Tendsto (fun r => 1 + (q (l * r) - q r) / q r) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hdiff
    apply hone.congr'
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hqr := (hqpos r hr).ne'
    field_simp
    ring
  constructor
  · filter_upwards [eventually_ge_atTop r₀] with r hr
    exact (hqpos r hr).ne'
  · intro l hl
    simp only [Real.rpow_zero]
    rcases le_or_gt 1 l with hl1 | hl1
    · exact hbase l hl1
    · have hlinv : 1 ≤ l⁻¹ := by
        rw [le_inv_comm₀ one_pos hl]
        simpa using hl1.le
      have h := hbase l⁻¹ hlinv
      have hcomp : Tendsto (fun x : ℝ => q (l⁻¹ * (l * x)) / q (l * x)) atTop (𝓝 1) :=
        h.comp ((tendsto_const_mul_atTop_of_pos hl).2 tendsto_id)
      have hcomp' : Tendsto (fun x : ℝ => q x / q (l * x)) atTop (𝓝 1) := by
        refine hcomp.congr' ?_
        filter_upwards with x
        rw [show l⁻¹ * (l * x) = x by field_simp]
      have hinv := hcomp'.inv₀ one_ne_zero
      have hfin : Tendsto (fun x => (q x / q (l * x))⁻¹) atTop (𝓝 1) := by
        simpa using hinv
      refine hfin.congr' ?_
      filter_upwards with x
      exact inv_div (q x) (q (l * x))

/-- **Lemma I.5.5 in the critical case `a = b`**, with no additional global
measurability premise on `f`. -/
theorem lemma_I_5_5_of_eq {f f' : ℝ → ℝ} (D : RVPosData h a)
    (ha : 0 < a) (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f a ∧ Tendsto (fun r => h r / f r) atTop (𝓝 0) ∧
      Tendsto (fun r => f' r / (a * f r / r)) atTop (𝓝 1) := by
  obtain ⟨r₀, δ, hr₀, hr₀1, hrD, hδm, hδ0, hδ1, hode⟩ :=
    exists_shared_error_of_tendsto D ha hpos hfpos hderiv hasym
  let w := powerExpWeight r₀ a δ
  let v : ℝ → ℝ := fun s => h s / w s
  let g : ℝ → ℝ := fun s => v s / s
  let F : ℝ → ℝ := fun s => (1 - δ s) * g s
  let q : ℝ → ℝ := fun r => f r * (w r)⁻¹
  have hwrv : RegularlyVaryingAtTop w a :=
    regularlyVarying_powerExpWeight ha hr₀ hδm hδ0 hδ1
  have hwm : Measurable w := measurable_powerExpWeight hr₀ hδm hδ1
  have hwpos : ∀ s, 0 < s → 0 < w s := by
    intro s hs
    dsimp [w, powerExpWeight]
    exact mul_pos (Real.rpow_pos_of_pos hs a) (Real.exp_pos _)
  have hvrv : RegularlyVaryingAtTop v 0 := by
    have hh := D.rv.mul hwrv.inv
    have hidx : a + -a = 0 := by ring
    rw [hidx] at hh
    simpa [v, div_eq_mul_inv] using hh
  have hvm : Measurable v := D.measurable_f.div hwm
  have hvpos : ∀ x, r₀ ≤ x → 0 < v x := by
    intro x hx
    exact div_pos (D.pos_above x (hrD.trans hx)) (hwpos x (hr₀.trans_le hx))
  have hgm : Measurable g := hvm.div measurable_id
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
      apply intervalIntegrable_of_bound D.measurable_f.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
      rw [uIcc_of_le hxy] at hs
      rw [Real.norm_eq_abs, abs_of_pos (hpos s (hr₀.trans_le (hx.trans hs.1)))]
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
  have hFint_of_le : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable F volume x y := by
    intro x y hx hxy
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    have hgi : IntegrableOn g (Icc x y) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)).1 (hgint x y hx hxy)
    have hmae : AEStronglyMeasurable (fun s => 1 - δ s) (volume.restrict (Icc x y)) :=
      (measurable_const.sub hδm).aestronglyMeasurable
    have hbdd : ∀ᵐ s ∂(volume.restrict (Icc x y)), ‖1 - δ s‖ ≤ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      have hd := hδ1 s (hx.trans hs.1)
      calc ‖1 - δ s‖ = |1 - δ s| := Real.norm_eq_abs _
        _ ≤ |1| + |δ s| := abs_sub _ _
        _ ≤ 2 := by rw [abs_one]; linarith
    exact hgi.bdd_mul hmae hbdd
  have hFint : ∀ x y : ℝ, r₀ ≤ x → r₀ ≤ y → IntervalIntegrable F volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · exact hFint_of_le x y hx hxy
    · exact (hFint_of_le y x hy hyx).symm
  have hqinc : ∀ R, r₀ ≤ R → q R - q r₀ = ∫ s in r₀..R, F s := by
    intro R hR
    simpa [q, F, g, v, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      normalized_increment_of_driving_ode (D := D) (a := a) (r₀ := r₀) (R := R)
        ha hr₀ hR hrD (fun x hx => hderiv x (hr₀.trans_le hx)) hδm hδ1 hode
  have hq₀ : 0 < q r₀ := by
    dsimp [q]
    exact mul_pos (hfpos r₀ hr₀) (inv_pos.mpr (hwpos r₀ hr₀))
  obtain ⟨hqv, hvq, hqrv⟩ := critical_primitive_properties hr₀ hvm hvrv hvpos
    hδ0 hδ1 (fun x hx => rfl) hFint hq₀ hqinc
  have hwprod : RegularlyVaryingAtTop (fun r => w r * q r) a := by
    simpa using hwrv.mul hqrv
  have hfrv : RegularlyVaryingAtTop f a := hwprod.congr_of_eventuallyEq (by
    filter_upwards [hwrv.1] with r hr
    dsimp [q]
    field_simp [hr])
  have hf0 : Tendsto (fun r => h r / f r) atTop (𝓝 0) := by
    apply hvq.congr'
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hw := (hwpos r (hr₀.trans_le hr)).ne'
    have hh := (D.pos_above r (hrD.trans hr)).ne'
    dsimp [v, q]
    field_simp
  refine ⟨hfrv, hf0, ?_⟩
  have htotal : Tendsto (fun r => (a * f r + h r) / (a * f r)) atTop (𝓝 1) := by
    have hz : Tendsto (fun r => 1 + a⁻¹ * (h r / f r)) atTop (𝓝 1) := by
      simpa using (hf0.const_mul a⁻¹).const_add 1
    apply hz.congr'
    filter_upwards [hfrv.1] with r hr
    field_simp [ha.ne', hr]
  have hterm : Tendsto (fun r => (1 - δ r) * ((a * f r + h r) / (a * f r)))
      atTop (𝓝 1) := by
    have hd := (tendsto_const_nhds (x := (1 : ℝ))).sub hδ0
    have hm := hd.mul htotal
    simpa using hm
  apply hterm.congr'
  filter_upwards [eventually_ge_atTop r₀, hfrv.1] with r hr hfr
  have hrpos : 0 < r := hr₀.trans_le hr
  rw [hode r hr]
  field_simp [ha.ne', hfr, hrpos.ne']


/-- **Lemma I.5.5**, in the source's measurable positive-driver form. -/
theorem lemma_I_5_5 {f f' h : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f (max a b) ∧ (b ≤ a →
      Tendsto (fun r => h r / f r) atTop (𝓝 0) ∧
        Tendsto (fun r => f' r / (a * f r / r)) atTop (𝓝 1)) := by
  have hhe : ∀ᶠ x in atTop, 0 < h x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hpos x hx
  let D : RVPosData h b := RVPosData.of hb hhm hhrv hhe
  rcases lt_trichotomy b a with hba | heq | hab
  · obtain ⟨hfrv, hf0, hder⟩ := lemma_I_5_5_of_lt D ha hba hpos hfpos hderiv hasym
    refine ⟨?_, fun _ => ⟨hf0, hder⟩⟩
    simpa [max_eq_left hba.le] using hfrv
  · subst b
    obtain ⟨hfrv, hf0, hder⟩ := lemma_I_5_5_of_eq D ha hpos hfpos hderiv hasym
    refine ⟨?_, fun _ => ⟨hf0, hder⟩⟩
    simpa using hfrv
  · have hfrv := lemma_I_4_21_regularlyVarying_of_hasDerivAt D ha hab hpos hfpos hderiv hasym
    refine ⟨?_, fun hle => (not_le_of_gt hab hle).elim⟩
    simpa [max_eq_right hab.le] using hfrv

#print axioms PercLib.CriticalLRP.Analysis.eventually_slowlyVarying_right_le_two
#print axioms PercLib.CriticalLRP.Analysis.eventually_half_le_slowlyVarying_left
#print axioms PercLib.CriticalLRP.Analysis.eventually_critical_window_lower
#print axioms PercLib.CriticalLRP.Analysis.tendsto_critical_ratio_atTop
#print axioms PercLib.CriticalLRP.Analysis.critical_primitive_properties
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_5_of_eq
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_5_5

end PercLib.CriticalLRP.Analysis
