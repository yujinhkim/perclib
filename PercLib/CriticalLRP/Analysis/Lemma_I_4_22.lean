/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.4.22: a one-sided estimate for the driven ODE

Source: Tom Hutchcroft, *Critical long-range percolation I*, Lemma I.4.22.
The comparison is made at an intermediate power `c` with `a < c < b`.
The normalized increment is bounded from above by the derivative majorant,
using `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`, so no
nonnegative-derivative or derivative-continuity hypothesis is introduced.

The Karamata denominator is the unweighted `h/r^(c+1)`.  Its index is
`b-c-1 > -1`.  Positive normalization means that the initial-value term
vanishes, and gives `f/h ≤ 1/(b-c)+o(1)`.  Choosing `c` after the desired
error budget, and writing `(1+ ε) = (1+t)^2`, converts this into the exact
source inequality `f(r) ≤ (1+ε) h(r)/(b-a)` eventually.  The positivity of `f` is explicit. The proof uses the source's one-sided
inequality, not the two-sided convergence of Lemma I.4.21.
-/
module

public import PercLib.CriticalLRP.Analysis.KaramataTail
public import PercLib.CriticalLRP.Analysis.Lemma_I_4_21

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

/-- A function tending to one is regularly varying with index zero. -/
theorem regularlyVarying_of_tendsto_one {θ : ℝ → ℝ} (hθ : Tendsto θ atTop (𝓝 1)) :
    RegularlyVaryingAtTop θ 0 := by
  constructor
  · exact hθ.eventually (eventually_gt_nhds zero_lt_one) |>.mono (fun x hx => hx.ne')
  · intro l hl
    have hscale : Tendsto (fun x : ℝ => l * x) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hl).mpr tendsto_id
    have ht : Tendsto (fun x => θ (l * x) / θ x) atTop (𝓝 ((1 : ℝ) / 1)) :=
      (hθ.comp hscale).div hθ one_ne_zero
    simpa using ht

/-- The increment bound behind the inequality version of the driven ODE. -/
theorem normalized_increment_le_of_driving_bound {f f' θ : ℝ → ℝ} (D : RVPosData h b)
    {a c r₀ : ℝ} (ha : 0 < a)
    (hr₀ : 0 < r₀) (hrD : D.threshold ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hfpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hθm : Measurable θ) (hθlower : ∀ x, r₀ ≤ x → 1 ≤ θ x)
    (hθupper : ∀ x, r₀ ≤ x → θ x ≤ min 2 (c / a))
    (hfbd : ∀ x, r₀ ≤ x → f' x ≤ θ x * (a * f x + h x) / x)
    {R : ℝ} (hR : r₀ ≤ R) :
    ((f R / R ^ c - f r₀ / r₀ ^ c) ≤
      ∫ s in r₀..R, θ s * h s / s ^ (c + 1)) ∧ (IntervalIntegrable (fun s => θ s * h s / s ^ (c + 1)) volume r₀ R) := by
  let q : ℝ → ℝ := fun r => f r / r ^ c
  let g : ℝ → ℝ := fun s => θ s * h s / s ^ (c + 1)
  have hw : ∀ x ∈ uIcc r₀ R,
      HasDerivAt q ((f' x * x - c * f x) / x ^ (c + 1)) x := by
    intro x hx
    rw [uIcc_of_le hR] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
    have hp : x ^ c ≠ 0 := (Real.rpow_pos_of_pos hx0 c).ne'
    have hd := (hderiv x hx.1).div (Real.hasDerivAt_rpow_const (x := x) (p := c)
      (Or.inl hx0.ne')) hp
    apply hd.congr_deriv
    have hc1 : x ^ (c + 1) = x ^ c * x := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    have hc2 : x ^ (c - 1) = x ^ c / x := Real.rpow_sub_one hx0.ne' c
    rw [hc1, hc2]
    field_simp [hd]
  have hqbound : ∀ x ∈ Ioo r₀ R, (f' x * x - c * f x) / x ^ (c + 1) ≤ g x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1.le
    have hf := hfpos x hx.1.le
    have haθ : a * θ x ≤ c := by
      have ht := hθupper x hx.1.le
      have ht' : θ x ≤ c / a := ht.trans (min_le_right _ _)
      calc a * θ x ≤ a * (c / a) := mul_le_mul_of_nonneg_left ht' ha.le
        _ = c := by field_simp
    have hf1 : f' x * x ≤ θ x * (a * f x + h x) :=
      (le_div_iff₀ hx0).mp (hfbd x hx.1.le)
    have he : f' x * x - c * f x ≤ θ x * h x := by
      have hθα : a * θ x * f x ≤ c * f x :=
        mul_le_mul_of_nonneg_right haθ hf.le
      nlinarith
    have hp : 0 < x ^ (c + 1) := Real.rpow_pos_of_pos hx0 (c + 1)
    exact (div_le_div_iff_of_pos_right hp).2 he
  have hM1 : 1 ≤ min 2 (c / a) :=
    (hθlower r₀ le_rfl).trans (hθupper r₀ le_rfl)
  have hgint : IntervalIntegrable g volume r₀ R := by
    obtain ⟨C, hC⟩ := D.bddAbove_Icc R
    have hbase : IntervalIntegrable (fun s => θ s * h s) volume r₀ R := by
      apply intervalIntegrable_of_bound (C := min 2 (c / a) * C)
        (hθm.mul D.measurable_f).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with x hx
      rw [uIcc_of_le hR] at hx
      have hxD := le_trans hrD hx.1
      have hhpos := D.pos_above x hxD
      have hθpos : 0 < θ x := zero_lt_one.trans_le (hθlower x hx.1)
      have hθle : θ x ≤ min 2 (c / a) := hθupper x hx.1
      calc ‖θ x * h x‖ = θ x * h x := by rw [Real.norm_eq_abs, abs_of_pos (mul_pos hθpos hhpos)]
        _ ≤ min 2 (c / a) * C := mul_le_mul hθle (hC x hxD hx.2) hhpos.le (by linarith)
    have hIc : IntegrableOn (fun s => θ s * h s) (Icc r₀ R) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hR (by finiteness)).1 hbase
    have hcont : ContinuousOn (fun x : ℝ => (x ^ (c + 1))⁻¹) (Icc r₀ R) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
      exact (Real.continuousAt_rpow_const x (c + 1) (Or.inl hx0.ne')).inv₀
        (Real.rpow_pos_of_pos hx0 _).ne' |>.continuousWithinAt
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hR (by simp)]
    simpa [g, div_eq_mul_inv] using hIc.mul_continuousOn hcont isCompact_Icc
  have hqcont : ContinuousOn q (Icc r₀ R) := by
    intro x hx
    exact (hw x (by rw [uIcc_of_le hR]; exact hx)).continuousAt.continuousWithinAt
  refine ⟨?_, hgint⟩
  exact intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hR hqcont
    (fun x hx => (hw x (by rw [uIcc_of_le hR]; exact ⟨hx.1.le, hx.2.le⟩)).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hR (by simp)).1 hgint) hqbound

/-- The intermediate-power estimate for the inequality version of the driven ODE. -/
theorem eventually_ratio_le_of_driving_bound {f f' θ : ℝ → ℝ} (D : RVPosData h b)
    {a c r₀ : ℝ} (ha : 0 < a) (hac : a < c) (hcb : c < b)
    (hr₀ : 0 < r₀) (hr₀1 : 1 ≤ r₀) (hrD : D.threshold ≤ r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hfpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hθm : Measurable θ) (hθlower : ∀ x, r₀ ≤ x → 1 ≤ θ x)
    (hθupper : ∀ x, r₀ ≤ x → θ x ≤ min 2 (c / a))
    (hθ0 : Tendsto θ atTop (𝓝 1))
    (hfbd : ∀ x, r₀ ≤ x → f' x ≤ θ x * (a * f x + h x) / x) :
    ∀ ε > 0, ∀ᶠ r in atTop, f r / h r ≤ 1 / (b - c) + ε := by
  let B : ℝ → ℝ := fun s => h s / s ^ (c + 1)
  let V : ℝ → ℝ := fun r => h r / r ^ c
  let q : ℝ → ℝ := fun r => f r / r ^ c
  let g : ℝ → ℝ := fun s => θ s * B s
  let t : ℝ := 1 / (b - c)
  have hBrv : RegularlyVaryingAtTop B (b - c - 1) := by
    have hb := D.rv.mul (regularlyVaryingAtTop_rpow (c + 1)).inv
    have hidx : b + -(c + 1) = b - c - 1 := by ring
    rw [hidx] at hb
    simpa [B, div_eq_mul_inv, mul_assoc] using hb
  have hgm : Measurable B := D.measurable_f.div (by fun_prop)
  have hgp : ∀ᶠ s in atTop, 0 < B s := by
    filter_upwards [eventually_ge_atTop r₀] with s hs
    exact div_pos (D.pos_above s (le_trans hrD hs))
      (Real.rpow_pos_of_pos (lt_of_lt_of_le hr₀ hs) _)
  have hgint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable B volume x y := by
    intro x y hx hxy
    obtain ⟨C, hC⟩ := D.bddAbove_Icc y
    have hh : IntervalIntegrable h volume x y := by
      apply intervalIntegrable_of_bound D.measurable_f.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
      rw [uIcc_of_le hxy] at hs
      rw [Real.norm_eq_abs, abs_of_pos (D.pos_above s (le_trans hrD hx |>.trans hs.1))]
      exact hC s (le_trans hrD hx |>.trans hs.1) hs.2
    have hIc : IntegrableOn h (Icc x y) volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by finiteness)).1 hh
    have hcont : ContinuousOn (fun s : ℝ => (s ^ (c + 1))⁻¹) (Icc x y) := by
      intro s hs
      have hs0 : 0 < s := (lt_of_lt_of_le hr₀ hx).trans_le hs.1
      exact (Real.continuousAt_rpow_const s (c + 1) (Or.inl hs0.ne')).inv₀
        (Real.rpow_pos_of_pos hs0 _).ne' |>.continuousWithinAt
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    simpa [B, div_eq_mul_inv] using hIc.mul_continuousOn hcont isCompact_Icc
  have hδm : Measurable (fun s => 1 - θ s) := measurable_const.sub hθm
  have hδ0 : Tendsto (fun s => 1 - θ s) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hθ0
  have hδ1 : ∀ x, r₀ ≤ x → |1 - θ x| ≤ 1 := by
    intro x hx
    have hlo := hθlower x hx
    have hhi := (hθupper x hx).trans (min_le_left _ _)
    rw [abs_le]
    constructor <;> linarith
  have hK : Tendsto (fun r => (∫ s in r₀..r, g s) / (r * B r))
      atTop (𝓝 t) := by
    have hk := tendsto_mul_one_sub_karamata_integral_tail (g := B) (δ := fun s => 1 - θ s)
      (by linarith : -1 < b - c - 1) hr₀ hr₀1 hgm hBrv hgp hgint hδm hδ0 hδ1
    simpa only [sub_sub_cancel, sub_add_cancel, t, B, g] using hk
  have hq0 : Tendsto (fun r => q r₀ / (r * B r)) atTop (𝓝 0) := by
    have hVrv : RegularlyVaryingAtTop V (b - c) := by
      have hd := D.rv.mul (regularlyVaryingAtTop_rpow c).inv
      have hidx : b + -c = b - c := by ring
      rw [hidx] at hd
      simpa [V, div_eq_mul_inv, mul_assoc] using hd
    have hVpos : ∀ᶠ r in atTop, 0 < V r := by
      filter_upwards [eventually_ge_atTop r₀] with r hr
      exact div_pos (D.pos_above r (le_trans hrD hr))
        (Real.rpow_pos_of_pos (lt_of_lt_of_le hr₀ hr) _)
    let Dg := RVPosData.of (by linarith : 0 < b - c)
      (D.measurable_f.div (by fun_prop)) hVrv hVpos
    have hi := Dg.tendsto_atTop_self.inv_tendsto_atTop.const_mul (q r₀)
    rw [mul_zero] at hi
    apply hi.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    dsimp [B, V]
    rw [Real.rpow_add hr, Real.rpow_one]
    field_simp
  have hbound : ∀ᶠ r in atTop, q r / (r * B r) ≤
      (∫ s in r₀..r, g s) / (r * B r) + q r₀ / (r * B r) := by
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hi := (normalized_increment_le_of_driving_bound D ha hr₀ hrD hderiv hfpos hθm
      hθlower hθupper hfbd hr).1
    have hq : q r ≤ (∫ s in r₀..r, g s) + q r₀ := by
      simpa [g, B, mul_div_assoc] using hi
    have hposden : 0 < r * B r := by
      exact mul_pos (lt_of_lt_of_le hr₀ hr)
        (div_pos (D.pos_above r (le_trans hrD hr))
          (Real.rpow_pos_of_pos (lt_of_lt_of_le hr₀ hr) _))
    calc q r / (r * B r) ≤ ((∫ s in r₀..r, g s) + q r₀) / (r * B r) :=
      div_le_div_of_nonneg_right hq hposden.le
    _ = (∫ s in r₀..r, g s) / (r * B r) + q r₀ / (r * B r) := by rw [add_div]
  have hlim : Tendsto (fun r => (∫ s in r₀..r, g s) / (r * B r) + q r₀ / (r * B r))
      atTop (𝓝 t) := by
    have hl := hK.add hq0
    rw [add_zero] at hl
    exact hl
  have hbase : ∀ᶠ r in atTop, q r / (r * B r) = f r / h r := by
    filter_upwards [eventually_ge_atTop r₀] with r hr
    have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
    have hh := D.pos_above r (le_trans hrD hr)
    dsimp [q, B]
    rw [Real.rpow_add hrpos, Real.rpow_one]
    field_simp [hh.ne', hrpos.ne']
  intro ε hε
  have hupper : ∀ᶠ r in atTop, (∫ s in r₀..r, g s) / (r * B r) + q r₀ / (r * B r) < t + ε :=
    hlim.eventually (Iio_mem_nhds (show t < t + ε by linarith))
  filter_upwards [hbound, hupper, hbase] with r hb hu heq
  calc f r / h r = q r / (r * B r) := heq.symm
    _ ≤ (∫ s in r₀..r, g s) / (r * B r) + q r₀ / (r * B r) := hb
    _ ≤ t + ε := hu.le

/-- Construct the normalized one-sided error from the `(1+o(1))` hypothesis. -/
theorem exists_normalized_error_of_bounded_ratio {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a : ℝ} (ha : 0 < a)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hfbd : ∀ ε > 0, ∀ᶠ x in atTop,
      f' x ≤ (1 + ε) * (a * f x + h x) / x) :
    ∃ θ, Measurable θ ∧ (∀ x, 0 < x → 1 ≤ θ x) ∧ Tendsto θ atTop (𝓝 1) ∧
      ∀ x, 0 < x → f' x ≤ θ x * (a * f x + h x) / x := by
  let f₀ : ℝ → ℝ := fun r => if 0 < r then f r else 0
  have hf0m : Measurable f₀ := measurable_ite_pos_of_hasDerivAt hderiv
  have hf0eq : ∀ x, 0 < x → f₀ x = f x := by intro x hx; simp [f₀, hx]
  have hf0d : ∀ x, 0 < x → HasDerivAt f₀ (f' x) x := by
    intro x hx
    apply (hderiv x hx).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [f₀, Set.mem_Ioi.1 hy]
  have hq : ∀ ε > 0, ∀ᶠ x in atTop, deriv f₀ x * x / (a * f₀ x + h x) ≤ 1 + ε := by
    intro ε hε
    have hb := hfbd ε hε
    filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    have hden : 0 < a * f x + h x := by
      exact add_pos (mul_pos ha (hfpos x hxpos)) (hpos x hxpos)
    have hf := (le_div_iff₀ hxpos).mp hx
    have hz : f' x * x / (a * f x + h x) ≤ 1 + ε := by
      exact (div_le_iff₀ hden).2 hf
    rw [(hf0d x hxpos).deriv, hf0eq x hxpos]
    exact hz
  let θ : ℝ → ℝ := (Ioi 0).indicator (fun r => max 1 (deriv f₀ r * r / (a * f₀ r + h r)))
  have hθge : ∀ x, 0 < x → 1 ≤ θ x := by
    intro x hx
    simp [θ, hx, le_max_left]
  have hθz : ∀ x, 0 < x → deriv f₀ x * x / (a * f₀ x + h x) ≤ θ x := by
    intro x hx
    simp [θ, hx, le_max_right]
  have hθm : Measurable θ := by
    apply Measurable.indicator _ measurableSet_Ioi
    exact measurable_const.max (((measurable_deriv f₀).mul measurable_id).div
      ((measurable_const.mul hf0m).add D.measurable_f))
  refine ⟨θ, hθm, hθge, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.1 (hq (ε / 2) (by linarith))
    let Rcut := max R 1
    have hRcutpos : 0 < Rcut := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨Rcut, fun x hx => ?_⟩
    have hxpos : 0 < x := lt_of_lt_of_le hRcutpos hx
    have hnear : max 1 (deriv f₀ x * x / (a * f₀ x + h x)) ≤ 1 + ε / 2 := by
      have hRx := hR x (le_trans (le_max_left _ _) hx)
      exact max_le (by linarith) hRx
    have hθnear : θ x ≤ 1 + ε / 2 := by simpa [θ, hxpos] using hnear
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hθge x hxpos))]
    linarith
  · intro x hx
    have hden : 0 < a * f x + h x := add_pos (mul_pos ha (hfpos x hx)) (hpos x hx)
    have hz := hθz x hx
    have hid : f' x = (deriv f₀ x * x / (a * f₀ x + h x)) * (a * f x + h x) / x := by
      rw [(hf0d x hx).deriv, hf0eq x hx]
      field_simp [hden, hx]
    rw [hid]
    have hz' : (deriv f₀ x * x / (a * f₀ x + h x)) * (a * f x + h x) ≤
        θ x * (a * f x + h x) :=
      mul_le_mul_of_nonneg_right hz hden.le
    exact div_le_div_of_nonneg_right hz' hx.le

/-- **Lemma I.4.22**, with the one-sided asymptotic ODE in explicit eventual
`(1+ε)` form. -/
theorem lemma_I_4_22_of_hasDerivAt_bound {f f' : ℝ → ℝ} (D : RVPosData h b)
    {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hfbd : ∀ ε > 0, ∀ᶠ x in atTop,
      f' x ≤ (1 + ε) * (a * f x + h x) / x) :
    ∀ ε > 0, ∀ᶠ r in atTop, f r ≤ (1 + ε) * (h r / (b - a)) := by
  obtain ⟨θ, hθm, hθlower, hθ0, hfθbound⟩ :=
    exists_normalized_error_of_bounded_ratio D ha hpos hfpos hderiv hfbd
  intro ε hε
  let t : ℝ := Real.sqrt (1 + ε) - 1
  have hsqrt : 1 < Real.sqrt (1 + ε) := by
    have hsq0 : 0 ≤ Real.sqrt (1 + ε) := Real.sqrt_nonneg _
    by_contra! hn
    have hsle : Real.sqrt (1 + ε) ≤ 1 := hn
    have hsquare_le : (Real.sqrt (1 + ε)) ^ 2 ≤ 1 := by nlinarith
    have hsquare : (Real.sqrt (1 + ε)) ^ 2 = 1 + ε := Real.sq_sqrt (by linarith)
    linarith
  have ht : 0 < t := sub_pos.mpr hsqrt
  let c : ℝ := b - (b - a) / (1 + t)
  let q : ℝ := 1 / (b - c)
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hgt0 : 0 < 1 + t := by linarith
  have hlt : (b - a) / (1 + t) < b - a := by
    apply (div_lt_iff₀ hgt0).2
    nlinarith [mul_pos hgap ht]
  have hca : a < c := by
    have hq0 : 0 < (b - a) / (1 + t) := div_pos hgap hgt0
    dsimp [c]
    linarith
  have hcb : c < b := by
    have hq0 : 0 < (b - a) / (1 + t) := div_pos hgap hgt0
    dsimp [c]
    linarith
  have hbcc : b - c = (b - a) / (1 + t) := by dsimp [c]; ring
  have hsmall : 0 < min (c / a - 1) 1 := by
    have hac : 1 < c / a := (lt_div_iff₀ ha).2 (by simpa using hca)
    exact lt_min (sub_pos.mpr hac) one_pos
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 hθ0 (min (c / a - 1) 1) hsmall
  have hupper : ∀ x, R ≤ x → θ x ≤ min 2 (c / a) := by
    intro x hx
    have hd := hR x hx
    rw [Real.dist_eq] at hd
    have hd' := abs_lt.1 hd
    have hlt : θ x < 1 + min (c / a - 1) 1 := by linarith [hd'.1, hd'.2]
    have hca' : 1 + min (c / a - 1) 1 ≤ c / a := by
      have h0 := min_le_left (c / a - 1) 1
      linarith
    have hcc' : 1 + min (c / a - 1) 1 ≤ 2 := by
      have h0 := min_le_right (c / a - 1) 1
      linarith
    exact le_min (le_trans hlt.le hcc') (le_trans hlt.le hca')
  let R₀ := max 1 (max D.threshold R)
  have hR₀1 : 1 ≤ R₀ := le_max_left _ _
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le one_pos hR₀1
  have hR₀D : D.threshold ≤ R₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR₀R : R ≤ R₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hηpos : 0 < t / (b - a) := div_pos ht hgap
  have hu := eventually_ratio_le_of_driving_bound D ha hca hcb hR₀pos hR₀1 hR₀D
    (fun x hx => hderiv x (lt_of_lt_of_le hR₀pos hx))
    (fun x hx => hfpos x (lt_of_lt_of_le hR₀pos hx)) hθm (fun x hx => hθlower x (lt_of_lt_of_le hR₀pos hx))
    (fun x hx => hupper x (le_trans hR₀R hx)) hθ0 (fun x hx => hfθbound x (lt_of_lt_of_le hR₀pos hx))
    (t / (b - a)) hηpos
  have hba : (1 + t) * (b - c) = b - a := by
    rw [hbcc]
    field_simp
  have hbudget : (b - a) * (q + t / (b - a)) = 1 + 2 * t := by
    have hbc0 : 0 < b - c := sub_pos.mpr hcb
    rw [← hba]
    dsimp [q]
    field_simp [hbc0.ne', hgt0.ne']
    ring
  filter_upwards [hu, eventually_gt_atTop (0 : ℝ)] with r hu hr
  have hfactor : 0 < (1 + t) * (b - c) := mul_pos hgt0 (sub_pos.mpr hcb)
  have hmul := mul_le_mul_of_nonneg_left hu hfactor.le
  have hgf : (b - a) * (f r / h r) ≤ 1 + 2 * t := by
    calc (b - a) * (f r / h r) = ((1 + t) * (b - c)) * (f r / h r) := by rw [← hba]
      _ ≤ ((1 + t) * (b - c)) * (q + t / (b - a)) := by simpa [q] using hmul
      _ = (b - a) * (q + t / (b - a)) := by rw [hba]
      _ = 1 + 2 * t := hbudget
  have hden : 0 < h r / (b - a) := div_pos (hpos r hr) hgap
  have hne : h r ≠ 0 := (hpos r hr).ne'
  have heq : f r = (h r / (b - a)) * ((b - a) * (f r / h r)) := by
    field_simp [hne, hgap.ne']
  have hineq1 : (h r / (b - a)) * ((b - a) * (f r / h r)) ≤
      (h r / (b - a)) * (1 + 2 * t) :=
    mul_le_mul_of_nonneg_left hgf hden.le
  have hineq2 : (h r / (b - a)) * (1 + 2 * t) ≤ (h r / (b - a)) * (1 + ε) := by
    have hle : 1 + 2 * t ≤ 1 + ε := by
      have hsquare : (1 + t) ^ 2 = 1 + ε := by
        have hts : 1 + t = Real.sqrt (1 + ε) := by dsimp [t]; ring
        rw [hts]
        exact Real.sq_sqrt (by linarith)
      nlinarith [sq_nonneg t]
    exact mul_le_mul_of_nonneg_left hle hden.le
  have hcomm : (h r / (b - a)) * (1 + ε) = (1 + ε) * (h r / (b - a)) := by ring
  exact (heq.le.trans (hineq1.trans hineq2)).trans_eq hcomm

#print axioms PercLib.CriticalLRP.Analysis.regularlyVarying_of_tendsto_one
#print axioms PercLib.CriticalLRP.Analysis.normalized_increment_le_of_driving_bound
#print axioms PercLib.CriticalLRP.Analysis.eventually_ratio_le_of_driving_bound
#print axioms PercLib.CriticalLRP.Analysis.exists_normalized_error_of_bounded_ratio
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_4_22_of_hasDerivAt_bound

end PercLib.CriticalLRP.Analysis
