/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Almost-everywhere normalized derivative increments
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

/-- The exact normalized increment for an absolutely continuous solution with an
almost-everywhere derivative relation. No differentiability of the integrating weight
at exceptional points and no continuity of the signed measurable error is required. -/
theorem normalized_increment_of_driving_ode_ac {f f' h : ℝ → ℝ}
    {a r₀ R : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀) (hR : r₀ ≤ R)
    (hfAC : AbsolutelyContinuousOnInterval f r₀ R)
    (hderiv : ∀ᵐ x, x ∈ Ioc r₀ R → HasDerivAt f (f' x) x)
    (hδm : Measurable δ) (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hode : ∀ᵐ x, x ∈ Ioc r₀ R → f' x = (1 - δ x) * a * f x / x + h x / x) :
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
    filter_upwards [ae_hasDerivAt_powerExpWeight ha hr₀ hR hδm hδ1, hderiv, hode] with x hx hfDeriv hOde
    intro hxmem
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxmem.1.le
    have hwpos : 0 < w x := by
      dsimp [w, powerExpWeight]
      exact mul_pos (Real.rpow_pos_of_pos hxpos a) (Real.exp_pos _)
    have hw := hx hxmem
    have hq := (hfDeriv hxmem).mul (hw.inv hwpos.ne')
    have hqd : deriv q x = f' x * (w x)⁻¹ +
        f x * (-(a * (1 - δ x) * w x / x) / (w x) ^ 2) := hq.deriv
    rw [hqd, hOde hxmem]
    field_simp [hxpos.ne', hwpos.ne']
    ring
  calc (f R * (powerExpWeight r₀ a δ R)⁻¹) - (f r₀ * (powerExpWeight r₀ a δ r₀)⁻¹)
      = ∫ s in r₀..R, deriv q s := hqAC.integral_deriv_eq_sub.symm
    _ = ∫ s in r₀..R, h s / (s * powerExpWeight r₀ a δ s) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hqderiv] with x hx
        intro hxmem
        exact hx (by rwa [uIoc_of_le hR] at hxmem)




#print axioms PercLib.CriticalLRP.Analysis.normalized_increment_of_driving_ode_ac

end PercLib.CriticalLRP.Analysis
