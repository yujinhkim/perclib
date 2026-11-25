/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.4.21: the non-negligible driven ODE

Source: Tom Hutchcroft, *Critical long-range percolation I*, Lemma I.4.21
(p. 47 and the following page of the supplied paper).  The exact normalized
solution is proved using absolutely continuous primitives and an almost
everywhere fundamental theorem of calculus, not continuity of the error.

A zero extension of the signed error below its starting cut makes the primitive
continuous on the whole line.  The power times its exponential is identified
with the paper's integrating weight.  If the driving term has index `b` and
`0 < a < b`, the normalized driver `h/w` has index `b - a`, and its division by
`s` has index `b - a - 1 > -1`.  Karamata integration then gives `f/h → 1/(b-a)`.

The public derivative-ratio wrappers construct the signed measurable `δ → 0`
from the actual derivative ratio.  Positivity of `f` is an explicit premise at
those wrappers, as appropriate for the paper's volume-moment application.
The exact normalized solution and shared-error limit do not require it.
-/
module

public import PercLib.CriticalLRP.Analysis.KaramataTail
public import PercLib.CriticalLRP.Analysis.LogScaling

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

theorem absolutelyContinuousOnInterval_of_hasDerivAt_bounded {f f' : ℝ → ℝ} {a b C : ℝ}
    (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ uIcc a b, ‖f' x‖ ≤ C) :
    AbsolutelyContinuousOnInterval f a b := by
  have hC : 0 ≤ C := le_trans (norm_nonneg (f' a)) (hbound a left_mem_uIcc)
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨C, hC⟩)
  apply (convex_Icc _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  · intro x hx
    exact (hderiv x hx).hasDerivWithinAt
  · intro x hx
    exact_mod_cast hbound x hx

theorem absolutelyContinuousOnInterval_exp_of_bound {H : ℝ → ℝ} {a b B : ℝ}
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hB : ∀ x ∈ uIcc a b, |H x| ≤ B) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (H x)) a b := by
  let K : NNReal := ⟨Real.exp B, (Real.exp_pos B).le⟩
  have hK : LipschitzOnWith K Real.exp (Icc (-B) B) := by
    apply (convex_Icc _ _).lipschitzOnWith_of_nnnorm_deriv_le
    · intro x hx
      exact (Real.hasDerivAt_exp x).differentiableAt
    · intro x hx
      rw [Real.deriv_exp]
      have hnorm : ‖Real.exp x‖ ≤ (K : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
        exact Real.exp_le_exp.2 hx.2
      exact_mod_cast hnorm
  have hmap : MapsTo H (uIcc a b) (Icc (-B) B) := by
    intro x hx
    exact abs_le.1 (hB x hx)
  simpa [Function.comp_def] using hK.comp_absolutelyContinuousOnInterval hmap hH

/-- The error is set to zero to the left of its starting cut. -/
noncomputable def errorTail (r₀ : ℝ) (δ : ℝ → ℝ) : ℝ → ℝ := (Ioi r₀).indicator δ

/-- A regular variation weight with an exact error primitive. -/
noncomputable def powerExpWeight (r₀ a : ℝ) (δ : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ a * Real.exp (-(a * ∫ s in r₀..r, errorTail r₀ δ s / s))

theorem intervalIntegrable_errorTail_div {δ : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) (a b : ℝ) :
    IntervalIntegrable (fun s => errorTail r₀ δ s / s) volume a b := by
  have hfun : (fun s => errorTail r₀ δ s / s) = (Ioi r₀).indicator (fun s => δ s / s) := by
    funext s
    by_cases hs : r₀ < s <;> simp [errorTail, hs]
  rw [hfun]
  apply intervalIntegrable_indicator_Ioi_of_intervalIntegrable
  intro x y hx hxy
  exact (intervalIntegrable_div_of_bounded (lt_of_lt_of_le hr₀ hx) hxy hδm
    (fun t ht => hδ1 t (le_trans hx ht))).1

theorem measurable_errorTail {δ : ℝ → ℝ} {r₀ : ℝ} (hδm : Measurable δ) :
    Measurable (errorTail r₀ δ) := hδm.indicator measurableSet_Ioi

/-- The error primitive is continuous on the whole line. -/
theorem continuous_errorIntegral {δ : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) :
    Continuous (fun r => ∫ s in r₀..r, errorTail r₀ δ s / s) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_errorTail_div hr₀ hδm hδ1) r₀

theorem measurable_powerExpWeight {δ : ℝ → ℝ} {r₀ a : ℝ} (hr₀ : 0 < r₀)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) :
    Measurable (powerExpWeight r₀ a δ) := by
  have hpow : Measurable (fun r : ℝ => r ^ a) := by fun_prop
  exact hpow.mul (Real.measurable_exp.comp
    ((measurable_const.mul (continuous_errorIntegral hr₀ hδm hδ1).measurable).neg))

/-- On the positive tail, `powerExpWeight` differs from the paper's integrating
factor only by the positive constant `r₀ ^ a`. -/
theorem powerExpWeight_eq_of_le {δ : ℝ → ℝ} {r₀ a r : ℝ} (hr₀ : 0 < r₀)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) (hr : r₀ ≤ r) :
    powerExpWeight r₀ a δ r = r₀ ^ a *
      Real.exp (∫ s in r₀..r, (1 - errorTail r₀ δ s) * a / s) := by
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  let H : ℝ := ∫ s in r₀..r, errorTail r₀ δ s / s
  have herr : IntervalIntegrable (fun s => errorTail r₀ δ s / s) volume r₀ r :=
    intervalIntegrable_errorTail_div hr₀ hδm hδ1 r₀ r
  have herr' : IntervalIntegrable (fun s => a * (errorTail r₀ δ s / s)) volume r₀ r :=
    herr.const_mul a
  have hbase : IntervalIntegrable (fun s => a / s) volume r₀ r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr]
    intro s hs
    exact (ContinuousAt.div (continuousAt_const : ContinuousAt (fun _ : ℝ => a) s)
      continuousAt_id (ne_of_gt (lt_of_lt_of_le hr₀ hs.1))).continuousWithinAt
  have hlog : (∫ s in r₀..r, a / s) = Real.log (r / r₀) * a := by
    rw [show (fun s : ℝ => a / s) = (fun s => a * (1 / s)) by
      funext s; rw [mul_one_div], intervalIntegral.integral_const_mul,
      integral_one_div_of_pos hr₀ hrpos]
    ring
  have hsplit : (∫ s in r₀..r, (1 - errorTail r₀ δ s) * a / s) =
      Real.log (r / r₀) * a - a * H := by
    calc (∫ s in r₀..r, (1 - errorTail r₀ δ s) * a / s)
        = ∫ s in r₀..r, a / s - a * (errorTail r₀ δ s / s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          ring
      _ = (∫ s in r₀..r, a / s) - ∫ s in r₀..r, a * (errorTail r₀ δ s / s) :=
        intervalIntegral.integral_sub hbase herr'
      _ = Real.log (r / r₀) * a - a * H := by rw [hlog, intervalIntegral.integral_const_mul]
  have hW : Real.exp (∫ s in r₀..r, (1 - errorTail r₀ δ s) * a / s) =
      (r / r₀) ^ a * Real.exp (-(a * H)) := by
    rw [hsplit, show Real.log (r / r₀) * a - a * H =
      Real.log (r / r₀) * a + -(a * H) by ring,
      Real.exp_add, ← Real.rpow_def_of_pos (div_pos hrpos hr₀) a]
  calc powerExpWeight r₀ a δ r = r ^ a * Real.exp (-(a * H)) := rfl
    _ = r₀ ^ a * ((r / r₀) ^ a * Real.exp (-(a * H))) := by
        rw [Real.div_rpow hrpos.le hr₀.le]
        field_simp
    _ = r₀ ^ a * Real.exp (∫ s in r₀..r, (1 - errorTail r₀ δ s) * a / s) := by rw [← hW]

/-- The exact power/error weight is regularly varying of index `a`. -/
theorem regularlyVarying_powerExpWeight {δ : ℝ → ℝ} {r₀ a : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀) (hδm : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) :
    RegularlyVaryingAtTop (powerExpWeight r₀ a δ) a := by
  let d := errorTail r₀ δ
  let H : ℝ → ℝ := fun r => Real.exp (∫ s in r₀..r, (1 - d s) * a / s)
  have hdm : Measurable d := measurable_errorTail hδm
  have hdb : ∀ x, |d x| ≤ 1 := by
    intro x
    by_cases hx : r₀ < x
    · simpa [d, errorTail, hx] using hδ1 x hx.le
    · simp [d, errorTail, hx]
  have hd0 : Tendsto d atTop (𝓝 0) := by
    apply hδ0.congr'
    filter_upwards [eventually_gt_atTop r₀] with x hx
    simp [d, errorTail, hx]
  have hint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => (1 - d s) * a / s) volume x y := by
    intro x y hx hxy
    apply intervalIntegrable_div_of_bounded (g := fun s => (1 - d s) * a) (C := 2 * a)
      (lt_of_lt_of_le hr₀ hx) hxy ((measurable_const.sub hdm).mul_const a)
    intro s hs
    have hfac : |1 - d s| ≤ 2 := by
      calc |1 - d s| ≤ |1| + |d s| := abs_sub _ _
        _ ≤ 2 := by have hb := hdb s; rw [abs_one]; linarith
    calc |(1 - d s) * a| = |1 - d s| * a := by rw [abs_mul, abs_of_pos ha]
      _ ≤ 2 * a := mul_le_mul_of_nonneg_right hfac ha.le
  have hHrv : RegularlyVaryingAtTop H a :=
    regularlyVarying_exp_integral_of_tendsto_zero ha hr₀ hdm hd0 hint
  have hweight : ∀ r : ℝ, r₀ ≤ r → powerExpWeight r₀ a δ r = r₀ ^ a * H r := by
    intro r hr
    exact powerExpWeight_eq_of_le hr₀ hδm hδ1 hr
  constructor
  · filter_upwards [hHrv.1, eventually_ge_atTop r₀] with r hr hr₀r
    rw [hweight r hr₀r]
    exact mul_ne_zero (Real.rpow_pos_of_pos hr₀ a).ne' hr
  · intro l hl
    have hscale : Tendsto (fun x : ℝ => l * x) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hl).mpr tendsto_id
    apply (hHrv.2 l hl).congr'
    filter_upwards [hHrv.1, hscale.eventually hHrv.1, eventually_ge_atTop r₀,
      hscale.eventually (eventually_ge_atTop r₀)] with r hr hlr hr₀r hlr₀
    rw [hweight r hr₀r, hweight (l * r) hlr₀]
    field_simp

/-- Almost everywhere on a tail interval, the exact power/error weight solves
`w' = a (1-δ) w/r`. -/
theorem ae_hasDerivAt_powerExpWeight {δ : ℝ → ℝ} {r₀ a R : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) :
    ∀ᵐ x, x ∈ Ioc r₀ R → HasDerivAt (powerExpWeight r₀ a δ)
      (a * (1 - δ x) * powerExpWeight r₀ a δ x / x) x := by
  have hint := intervalIntegrable_errorTail_div hr₀ hδm hδ1 r₀ R
  filter_upwards [hint.ae_hasDerivAt_integral] with x hx
  intro hxmem
  have hxuIcc : x ∈ uIcc r₀ R := by
    rw [uIcc_of_le hR]
    exact Ioc_subset_Icc_self hxmem
  have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxmem.1.le
  have hh := hx hxuIcc r₀ left_mem_uIcc
  have hp := Real.hasDerivAt_rpow_const (x := x) (p := a) (Or.inl hxpos.ne')
  have he := (hh.const_mul a).neg.exp
  have hmul := hp.mul he
  apply hmul.congr_deriv
  have hdx : errorTail r₀ δ x = δ x := by simp [errorTail, hxmem.1]
  have hpow : x ^ a = x ^ (a - 1) * x := by
    calc x ^ a = x ^ (a - 1 + 1) := by congr 1; ring
      _ = x ^ (a - 1) * x ^ (1 : ℝ) := Real.rpow_add hxpos _ _
      _ = x ^ (a - 1) * x := by rw [Real.rpow_one]
  dsimp [powerExpWeight] at hmul ⊢
  rw [hdx, hpow]
  field_simp
  ring

/-- Positive real powers are absolutely continuous on intervals bounded away from zero. -/
theorem absolutelyContinuousOnInterval_rpow {r₀ R α : ℝ} (hr₀ : 0 < r₀) (hR : r₀ ≤ R) :
    AbsolutelyContinuousOnInterval (fun x : ℝ => x ^ α) r₀ R := by
  have hcont : ContinuousOn (fun x : ℝ => α * x ^ (α - 1)) (uIcc r₀ R) := by
    rw [uIcc_of_le hR]
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₀ hx.1)
    exact ((Real.continuousAt_rpow_const x (α - 1) (Or.inl hx0)).const_mul α).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hcont
  apply absolutelyContinuousOnInterval_of_hasDerivAt_bounded (C := C)
  · intro x hx
    rw [uIcc_of_le hR] at hx
    exact Real.hasDerivAt_rpow_const (x := x) (p := α) (Or.inl (ne_of_gt (lt_of_lt_of_le hr₀ hx.1)))
  · exact hC

/-- The exact normalized solution of the inhomogeneous ODE. -/
theorem normalized_increment_of_driving_ode {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a r₀ R : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hrD : D.threshold ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hode : ∀ x, r₀ ≤ x → f' x = (1 - δ x) * (a * f x + h x) / x) :
    (f R * (powerExpWeight r₀ a δ R)⁻¹) - (f r₀ * (powerExpWeight r₀ a δ r₀)⁻¹) =
      ∫ s in r₀..R, (1 - δ s) * (h s / (s * powerExpWeight r₀ a δ s)) := by
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
    have hsum : |a * f x + h x| ≤ a * Cf + Ch := by
      calc |a * f x + h x| ≤ |a * f x| + |h x| := abs_add_le _ _
        _ = a * |f x| + |h x| := by rw [abs_mul, abs_of_pos ha]
        _ ≤ a * Cf + Ch := add_le_add (mul_le_mul_of_nonneg_left hfx ha.le) hhx
    have hmul : |1 - δ x| * |a * f x + h x| ≤ 2 * (a * Cf + Ch) :=
      mul_le_mul hfac hsum (abs_nonneg _) (by norm_num)
    rw [hode x hx.1, Real.norm_eq_abs, abs_div, abs_of_pos hx0, abs_mul]
    calc |1 - δ x| * |a * f x + h x| / x ≤ 2 * (a * Cf + Ch) / x :=
      div_le_div_of_nonneg_right hmul hx0.le
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
      deriv q x = (1 - δ x) * (h x / (x * w x)) := by
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
    _ = ∫ s in r₀..R, (1 - δ s) * (h s / (s * powerExpWeight r₀ a δ s)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hqderiv] with x hx
        intro hxmem
        exact hx (by rwa [uIoc_of_le hR] at hxmem)

/-- Under the shared-error ODE, the driving term forces `f/h` to its I.4.21 limit. -/
theorem tendsto_div_of_driving_ode {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a r₀ : ℝ} (ha : 0 < a) (hab : a < b) (hr₀ : 0 < r₀) (hr₀1 : 1 ≤ r₀)
    (hrD : D.threshold ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hδm : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hode : ∀ x, r₀ ≤ x → f' x = (1 - δ x) * (a * f x + h x) / x) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (1 / (b - a))) := by
  let w := powerExpWeight r₀ a δ
  let v : ℝ → ℝ := fun s => h s / w s
  let g : ℝ → ℝ := fun s => v s / s
  let q : ℝ → ℝ := fun r => f r * (w r)⁻¹
  have hwrv : RegularlyVaryingAtTop w a := regularlyVarying_powerExpWeight ha hr₀ hδm hδ0 hδ1
  have hwm : Measurable w := measurable_powerExpWeight hr₀ hδm hδ1
  have hwpos : ∀ s, 0 < s → 0 < w s := by
    intro s hs
    dsimp [w, powerExpWeight]
    exact mul_pos (Real.rpow_pos_of_pos hs a) (Real.exp_pos _)
  have hvrv : RegularlyVaryingAtTop v (b - a) := by
    have h := D.rv.mul hwrv.inv
    have hidx : b + -a = b - a := by ring
    rw [hidx] at h
    simpa [v, div_eq_mul_inv] using h
  have hvm : Measurable v := D.measurable_f.div hwm
  have hvpos : ∀ᶠ s in atTop, 0 < v s := by
    filter_upwards [eventually_ge_atTop r₀] with s hs
    exact div_pos (D.pos_above s (le_trans hrD hs)) (hwpos s (lt_of_lt_of_le hr₀ hs))
  have hgrv : RegularlyVaryingAtTop g (b - a - 1) := by
    have h := hvrv.mul (regularlyVaryingAtTop_rpow 1).inv
    have hidx : b - a + -1 = b - a - 1 := by ring
    rw [hidx] at h
    simpa [g, v, div_eq_mul_inv, Real.rpow_one] using h
  have hgm : Measurable g := hvm.div measurable_id
  have hgp : ∀ᶠ s in atTop, 0 < g s := by
    filter_upwards [hvpos, eventually_gt_atTop (0 : ℝ)] with s hs hs0
    exact div_pos hs hs0
  have hwcont : ContinuousOn w (Ici r₀) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr₀ hs
    have he : ContinuousAt (fun r => Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) s := by
      apply Real.continuous_exp.continuousAt.comp
      exact ((continuous_errorIntegral hr₀ hδm hδ1).continuousAt.const_mul a).neg
    change ContinuousWithinAt (fun r => r ^ a * Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) (Ici r₀) s
    have hfun : (fun r : ℝ => r ^ a * Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) =
        (fun r : ℝ => r ^ a) * (fun r => Real.exp (-(a * ∫ t in r₀..r, errorTail r₀ δ t / t))) := by rfl
    rw [hfun]
    exact ((Real.continuousAt_rpow_const s a (Or.inl hs0.ne')).mul he).continuousWithinAt
  have hgint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := D.bddAbove_Icc y
    have hh : IntervalIntegrable h volume x y := by
      apply intervalIntegrable_of_bound D.measurable_f.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
      rw [uIcc_of_le hxy] at hs
      rw [Real.norm_eq_abs, abs_of_pos (D.pos_above s (le_trans hrD hx |>.trans hs.1))]
      exact hC s (le_trans hrD hx |>.trans hs.1) hs.2
    have hIc : IntegrableOn h (Icc x y) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)).1 hh
    have hcont : ContinuousOn (fun s => (s * w s)⁻¹) (Icc x y) := by
      apply (continuousOn_id.mul (hwcont.mono (fun s hs => le_trans hx hs.1))).inv₀
      intro s hs
      have hs0 : 0 < s := (lt_of_lt_of_le hr₀ hx).trans_le hs.1
      exact (mul_pos hs0 (hwpos s hs0)).ne'
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    simpa [g, v, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hIc.mul_continuousOn hcont isCompact_Icc
  have hK : Tendsto (fun r => (∫ s in r₀..r, (1 - δ s) * g s) / (r * g r))
      atTop (𝓝 (1 / (b - a))) := by
    have hk := tendsto_mul_one_sub_karamata_integral_tail (by linarith : -1 < b - a - 1)
      hr₀ hr₀1 hgm hgrv hgp (fun x y hx hxy => hgint x y hx hxy)
      hδm hδ0 (fun x hx => hδ1 x hx)
    convert hk using 1; ring
  have hvD : RVPosData v (b - a) := RVPosData.of (by linarith) hvm hvrv hvpos
  have hvinf : Tendsto v atTop atTop := hvD.tendsto_atTop_self
  have hq0 : Tendsto (fun r => q r₀ / (r * g r)) atTop (𝓝 0) := by
    have hq0' : Tendsto (fun r => q r₀ / v r) atTop (𝓝 0) := by
      have hi := hvinf.inv_tendsto_atTop.const_mul (q r₀)
      simpa [div_eq_mul_inv] using hi
    apply hq0'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    dsimp [g]
    field_simp [hr.ne']
  have hinc : ∀ᶠ r in atTop, q r - q r₀ = ∫ s in r₀..r, (1 - δ s) * g s := by
    filter_upwards [eventually_ge_atTop r₀] with r hr
    simpa [q, g, v, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      normalized_increment_of_driving_ode (D := D) (a := a) (r₀ := r₀) (R := r)
        ha hr₀ hr hrD hderiv hδm hδ1 hode
  have hqdiff : Tendsto (fun r => (q r - q r₀) / (r * g r)) atTop (𝓝 (1 / (b - a))) := by
    apply hK.congr'
    filter_upwards [hinc] with r hr
    rw [hr]
  have hq : Tendsto (fun r => q r / (r * g r)) atTop (𝓝 (1 / (b - a))) := by
    have hl := hqdiff.add hq0
    rw [add_zero] at hl
    apply hl.congr'
    filter_upwards [hgp, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    field_simp
    ring
  apply hq.congr'
  filter_upwards [hvpos, hgp, eventually_ge_atTop r₀] with r hv hg hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  have hw := hwpos r hrpos
  have hhr := D.pos_above r (le_trans hrD hr)
  have hrg : r * g r = v r := by dsimp [g]; field_simp [hrpos.ne']
  calc q r / (r * g r) = q r / v r := by rw [hrg]
    _ = f r / h r := by dsimp [q, v]; field_simp [hw.ne', hhr.ne']

/-- A function differentiable on the positive axis has a measurable extension by zero. -/
theorem measurable_ite_pos_of_hasDerivAt {f f' : ℝ → ℝ}
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x) :
    Measurable (fun r => if 0 < r then f r else 0) := by
  let f₀ : ℝ → ℝ := fun r => if 0 < r then f r else 0
  have hfc : ContinuousOn f₀ (Ioi 0) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.congr ((hderiv x hx).continuousAt)
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [f₀, Set.mem_Ioi.1 hy]
  have hopen : ∀ U : Set ℝ, IsOpen U → IsOpen (Ioi 0 ∩ f₀ ⁻¹' U) := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hloc := (hfc x hx.1) (hU.mem_nhds hx.2)
    rw [nhdsWithin_eq_nhds.2 (Ioi_mem_nhds hx.1)] at hloc
    filter_upwards [hloc, Ioi_mem_nhds hx.1] with y hyU hypos
    exact ⟨hypos, hyU⟩
  change Measurable f₀
  apply measurable_of_isOpen
  intro U hU
  by_cases hz : 0 ∈ U
  · have heq : f₀ ⁻¹' U = (Ioi 0 ∩ f₀ ⁻¹' U) ∪ Iic 0 := by
      ext x
      by_cases hx : 0 < x
      · simp [f₀, hx]
      · have hfx : f₀ x = 0 := by
          change (if 0 < x then f x else 0) = 0
          exact ite_eq_right (not_lt_of_ge (le_of_not_gt hx))
        simp [hfx, le_of_not_gt hx, hz]
    rw [heq]
    exact (hopen U hU).measurableSet.union measurableSet_Iic
  · have heq : f₀ ⁻¹' U = Ioi 0 ∩ f₀ ⁻¹' U := by
      ext x
      by_cases hx : 0 < x
      · simp [f₀, hx]
      · have hfx : f₀ x = 0 := by
          change (if 0 < x then f x else 0) = 0
          exact ite_eq_right (not_lt_of_ge (le_of_not_gt hx))
        simp [hfx, le_of_not_gt hx, hz]
    rw [heq]
    exact (hopen U hU).measurableSet

/-- The measurable signed error in the paper's asymptotic driving ODE. -/
theorem exists_shared_error_of_tendsto {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a : ℝ} (ha : 0 < a)
    (hpos : ∀ x, 0 < x → 0 < h x)
    (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    ∃ r₀ δ, 0 < r₀ ∧ 1 ≤ r₀ ∧ D.threshold ≤ r₀ ∧ Measurable δ ∧
      Tendsto δ atTop (𝓝 0) ∧ (∀ x, r₀ ≤ x → |δ x| ≤ 1) ∧
      ∀ x, r₀ ≤ x → f' x = (1 - δ x) * (a * f x + h x) / x := by
  let f₀ : ℝ → ℝ := fun r => if 0 < r then f r else 0
  have hf0m : Measurable f₀ := measurable_ite_pos_of_hasDerivAt hderiv
  have hf0eq : ∀ x, 0 < x → f₀ x = f x := by intro x hx; simp [f₀, hx]
  have hf0d : ∀ x, 0 < x → HasDerivAt f₀ (f' x) x := by
    intro x hx
    apply (hderiv x hx).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [f₀, Set.mem_Ioi.1 hy]
  have hnumpos : ∀ x, 0 < x → 0 < a * f₀ x + h x := by
    intro x hx
    exact add_pos (mul_pos ha (by simpa [hf0eq x hx] using hfpos x hx)) (hpos x hx)
  have hq : Tendsto (fun r => deriv f₀ r * r / (a * f₀ r + h r)) atTop (𝓝 1) := by
    apply hasym.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [(hf0d x hx).deriv, hf0eq x hx]
    field_simp [hnumpos x hx, hx]
  have hraw0 : Tendsto (fun r => 1 - deriv f₀ r * r / (a * f₀ r + h r)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hq
  let δ : ℝ → ℝ := (Ioi 0).indicator (fun r => 1 - deriv f₀ r * r / (a * f₀ r + h r))
  have hδm : Measurable δ := by
    apply Measurable.indicator _ measurableSet_Ioi
    exact measurable_const.sub (((measurable_deriv f₀).mul measurable_id).div
      ((measurable_const.mul hf0m).add D.measurable_f))
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    apply hraw0.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [δ, hx]
  have hode : ∀ x, 0 < x → f' x = (1 - δ x) * (a * f x + h x) / x := by
    intro x hx
    have hd : deriv f₀ x = f' x := (hf0d x hx).deriv
    have hdx : δ x = 1 - deriv f₀ x * x / (a * f₀ x + h x) := by
      simp [δ, hx]
    rw [hdx, hf0eq x hx, hd]
    have hden : 0 < a * f x + h x := by
      rw [← hf0eq x hx]
      exact hnumpos x hx
    field_simp [hden, hx]
    ring
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hδ0 1 one_pos
  let R₀ := max (max 1 D.threshold) B
  have hR₀1 : 1 ≤ R₀ := le_trans (le_max_left 1 D.threshold) (le_max_left _ _)
  have hR₀D : D.threshold ≤ R₀ := le_trans (le_max_right 1 D.threshold) (le_max_left _ _)
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le one_pos hR₀1
  have hR₀B : B ≤ R₀ := le_max_right _ _
  refine ⟨R₀, δ, hR₀pos, hR₀1, hR₀D, hδm, hδ0, ?_, ?_⟩
  · intro x hx
    have hb := hB x (le_trans hR₀B hx)
    rw [Real.dist_eq, sub_zero] at hb
    linarith
  · intro x hx
    exact hode x (lt_of_lt_of_le hR₀pos hx)

/-- **Lemma I.4.21, asymptotic-ratio form.**  Positivity of `f` is explicit:
that is the form used for the paper's volume moments. -/
theorem lemma_I_4_21_tendsto_of_hasDerivAt {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (h r / (b - a))) atTop (𝓝 1) := by
  obtain ⟨r₀, δ, hr₀, hr₀1, hrD, hδm, hδ0, hδ1, hode⟩ :=
    exists_shared_error_of_tendsto D ha hpos hfpos hderiv hasym
  have hlim := tendsto_div_of_driving_ode D ha hab hr₀ hr₀1 hrD
    (fun x hx => hderiv x (lt_of_lt_of_le hr₀ hx))
    hδm hδ0 hδ1 hode
  have hmul := hlim.const_mul (b - a)
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hmul' : (b - a) * (1 / (b - a)) = 1 := by field_simp [hne]
  rw [hmul'] at hmul
  apply hmul.congr'
  filter_upwards [D.rv.1] with r hr
  field_simp [hr, hne]

/-- **Lemma I.4.21, regular-variation conclusion.** -/
theorem lemma_I_4_21_regularlyVarying_of_hasDerivAt {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f b := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hGrv : RegularlyVaryingAtTop (fun r => h r / (b - a)) b := by
    constructor
    · filter_upwards [D.rv.1] with r hr
      exact div_ne_zero hr hne
    · intro l hl
      apply (D.rv.2 l hl).congr'
      filter_upwards [D.rv.1] with r hr
      field_simp [hr, hne]
  exact RegularlyVaryingAtTop.of_tendsto_div hGrv
    (lemma_I_4_21_tendsto_of_hasDerivAt D ha hab hpos hfpos hderiv hasym)

#print axioms PercLib.CriticalLRP.Analysis.normalized_increment_of_driving_ode
#print axioms PercLib.CriticalLRP.Analysis.tendsto_div_of_driving_ode
#print axioms PercLib.CriticalLRP.Analysis.exists_shared_error_of_tendsto
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_4_21_tendsto_of_hasDerivAt
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_4_21_regularlyVarying_of_hasDerivAt

end PercLib.CriticalLRP.Analysis
