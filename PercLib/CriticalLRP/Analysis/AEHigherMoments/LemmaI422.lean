/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`, direction (2).

Almost-everywhere (off-corner) forms of the two analytic engines of Lemma I.4.22:

* `ae_normalized_increment_le_of_driving_bound` — the normalized increment comparison, with the
  pointwise derivative hypothesis of
  `Analysis.Lemma_I_4_22.normalized_increment_le_of_driving_bound` replaced by absolute
  continuity on compact radius windows plus an a.e. derivative and an a.e. driving bound;
* `ae_eventually_ratio_le_of_driving_bound` — the Karamata endpoint
  `f r / h r ≤ 1/(b-c) + ε`, from the same a.e. inputs.

No derivative is claimed or used at an exceptional null set of radii.
-/
module

public import PercLib.CriticalLRP.Analysis.AEHigherMoments.Defs
public import PercLib.CriticalLRP.Analysis.AEHigherMoments.Increment
public import PercLib.CriticalLRP.Analysis.Lemma_I_4_22


/-! # Almost-everywhere higher-moment interface: LemmaI422 -/

set_option autoImplicit false
set_option linter.style.multiGoal false

open MeasureTheory Filter Set Topology
open scoped Topology

@[expose] public section

namespace PercLib.CriticalLRP.Analysis.AE

/-- **The normalized increment comparison of Lemma I.4.22, with an a.e. derivative.**

This is `normalized_increment_le_of_driving_bound` with

* `hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x` replaced by `AbsolutelyContinuousOnTail f r₀`
  plus `AeHasDerivAtOnTail f f' r₀`,
* `hfbd : ∀ x, r₀ ≤ x → f' x ≤ θ x (a f x + h x)/x` replaced by its a.e. form
  `AeDrivingBound f f' θ h a r₀`.

The algebraic step is applied only at the a.e. radii where the derivative exists, and the
integration uses `sub_le_integral_of_ae_hasDerivAt_of_le`. -/
theorem ae_normalized_increment_le_of_driving_bound {h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b)
    {f f' θ : ℝ → ℝ} {a c r₀ : ℝ} (ha : 0 < a)
    (hr₀ : 0 < r₀) (hrD : D.threshold ≤ r₀)
    (hac : AbsolutelyContinuousOnTail f r₀) (hae : AeHasDerivAtOnTail f f' r₀)
    (hfpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hθm : Measurable θ) (hθlower : ∀ x, r₀ ≤ x → 1 ≤ θ x)
    (hθupper : ∀ x, r₀ ≤ x → θ x ≤ min 2 (c / a))
    (hfbd : AeDrivingBound f f' θ h a r₀)
    {R : ℝ} (hR : r₀ ≤ R) :
    ((f R / R ^ c - f r₀ / r₀ ^ c) ≤
      ∫ s in r₀..R, θ s * h s / s ^ (c + 1)) ∧
      (IntervalIntegrable (fun s => θ s * h s / s ^ (c + 1)) volume r₀ R) := by
  let q : ℝ → ℝ := fun r => f r / r ^ c
  let g : ℝ → ℝ := fun s => θ s * h s / s ^ (c + 1)
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
      calc ‖θ x * h x‖ = θ x * h x := by
            rw [Real.norm_eq_abs, abs_of_pos (mul_pos hθpos hhpos)]
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
  have hacq : AbsolutelyContinuousOnInterval q r₀ R :=
    AbsolutelyContinuousOnInterval.div_rpow (hac R hR) hr₀ hR
  have hsub : Set.Icc r₀ R ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hr₀ hx.1
  have hd1 : ∀ᵐ x ∂(volume.restrict (Set.Icc r₀ R)), HasDerivAt f (f' x) x :=
    ae_restrict_Icc_of_ae_restrict_Ici (p := fun x => HasDerivAt f (f' x) x) (R := R) hae
  have haeq : ∀ᵐ x ∂(volume.restrict (Set.Icc r₀ R)),
      HasDerivAt q ((f' x * x - c * f x) / x ^ (c + 1)) x :=
    ae_hasDerivAt_div_rpow (s := Set.Icc r₀ R) measurableSet_Icc hsub hd1
  have hle : ∀ᵐ x ∂(volume.restrict (Set.Icc r₀ R)),
      ((f' x * x - c * f x) / x ^ (c + 1)) ≤ g x := by
    have hb := ae_restrict_Icc_of_ae_restrict_Ici
      (p := fun x => f' x ≤ θ x * (a * f x + h x) / x) (R := R) hfbd
    filter_upwards [hb, ae_restrict_mem measurableSet_Icc] with x hbnd hx
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
    have hθa : a * θ x ≤ c := by
      have ht := hθupper x hx.1
      have ht' : θ x ≤ c / a := ht.trans (min_le_right _ _)
      calc a * θ x ≤ a * (c / a) := mul_le_mul_of_nonneg_left ht' ha.le
        _ = c := by field_simp
    exact div_rpow_deriv_le_of_driving hx0 (hfpos x hx.1) hθa hbnd
  have hinc := sub_le_integral_of_ae_hasDerivAt_of_le hR hacq haeq hle hgint
  exact ⟨by simpa [q, g] using hinc, hgint⟩

/-- **The intermediate-power estimate of Lemma I.4.22 with an a.e. derivative.**

This is `eventually_ratio_le_of_driving_bound` with the pointwise derivative hypothesis replaced
by `AbsolutelyContinuousOnTail` plus `AeHasDerivAtOnTail`, and the pointwise driving bound by its
a.e. form `AeDrivingBound`. -/
theorem ae_eventually_ratio_le_of_driving_bound {h : ℝ → ℝ} {b : ℝ} (D : RVPosData h b)
    {f f' θ : ℝ → ℝ} {a c r₀ : ℝ} (ha : 0 < a) (_hac : a < c) (hcb : c < b)
    (hr₀ : 0 < r₀) (hr₀1 : 1 ≤ r₀) (hrD : D.threshold ≤ r₀)
    (hAC : AbsolutelyContinuousOnTail f r₀) (hAE : AeHasDerivAtOnTail f f' r₀)
    (hfpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hθm : Measurable θ) (hθlower : ∀ x, r₀ ≤ x → 1 ≤ θ x)
    (hθupper : ∀ x, r₀ ≤ x → θ x ≤ min 2 (c / a))
    (hθ0 : Tendsto θ atTop (𝓝 1))
    (hfbd : AeDrivingBound f f' θ h a r₀) :
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
    have hi := (ae_normalized_increment_le_of_driving_bound D ha hr₀ hrD hAC hAE hfpos hθm
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

end PercLib.CriticalLRP.Analysis.AE
