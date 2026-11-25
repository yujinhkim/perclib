/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.

Hutchcroft, *Critical long-range percolation I*, Lemma I.4.5 (p. 35).
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

/-!
# The three analytic comparison cases of Lemma I.4.5

We prove the upper comparison (1), the divergent lower comparison (2), and the
exact inverse/integral identity (3). Positive differentiability, not continuity
of the derivative, is enough. The auxiliary inverse-scale functions
`1/f − (A/α)r^(-α)` implement parts (1) and (2) without integrating an
arbitrary derivative.
-/

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP

open Filter Set MeasureTheory
open scoped Topology


/-- `IntegrableOn` on `uIcc a b` implies interval integrability on `a..b`. -/
theorem intervalIntegrable_of_integrableOn_uIcc {f : ℝ → ℝ} {a b : ℝ}
    (h : IntegrableOn f (uIcc a b) volume) : IntervalIntegrable f volume a b := by
  rw [IntervalIntegrable]
  refine ⟨h.mono_set ?_, h.mono_set ?_⟩
  · intro x hx
    exact ⟨le_trans (min_le_left _ _) hx.1.le, le_trans hx.2 (le_max_right _ _)⟩
  · intro x hx
    exact ⟨le_trans (min_le_right _ _) hx.1.le, le_trans hx.2 (le_max_left _ _)⟩

/-- A measurable function bounded on `uIcc a b` is interval integrable on `a..b`. -/
theorem intervalIntegrable_of_bound {f : ℝ → ℝ} {a b C : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (uIcc a b)))
    (hC : ∀ᵐ x ∂(volume.restrict (uIcc a b)), ‖f x‖ ≤ C) :
    IntervalIntegrable f volume a b :=
  intervalIntegrable_of_integrableOn_uIcc
    (IntegrableOn.of_bound (isCompact_uIcc (a := a) (b := b)).measure_lt_top hmeas C hC)

/-- **Lemma I.4.5(1)** without a continuity hypothesis on `f'`:
if `f > 0` and `f'(r) ≥ A r^{-α-1} f(r)²` for all `r ≥ r₀`, then
`f(r) ≤ (α/A) r^α` for all `r ≥ r₀`. -/
theorem lemma_I_4_5_one_nocont {f f' : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hineq : ∀ x, r₀ ≤ x → A * x ^ (-α - 1) * (f x) ^ 2 ≤ f' x) :
    ∀ r, r₀ ≤ r → f r ≤ α / A * r ^ α := by
  -- the auxiliary function
  set H : ℝ → ℝ := fun x => (f x)⁻¹ - (A / α) * x ^ (-α) with hH
  -- its derivative on `(r₀, ∞)`
  have hHderiv : ∀ x, r₀ < x → HasDerivAt H (-(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1))) x := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have h1 : HasDerivAt (fun y => (f y)⁻¹) (-(f' x / (f x) ^ 2)) x := by
      have := (hderiv x hxr).inv (ne_of_gt (hpos x hxr))
      rwa [neg_div] at this
    have h2 : HasDerivAt (fun y : ℝ => x ^ (-α)) 0 x := hasDerivAt_const x _
    have h3 : HasDerivAt (fun y : ℝ => (A / α) * y ^ (-α))
        ((A / α) * (-α * x ^ (-α - 1))) x :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hxpos))).const_mul (A / α)
    exact h1.sub h3
  -- the derivative is nonpositive
  have hHnonpos : ∀ x, r₀ < x → -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1)) ≤ 0 := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have hfpos : 0 < f x := hpos x hxr
    have hsq : 0 < (f x) ^ 2 := by positivity
    have hineq' : A * x ^ (-α - 1) ≤ f' x / (f x) ^ 2 := by
      rw [le_div_iff₀ hsq]
      exact hineq x hxr
    have hAα : A / α * α = A := by field_simp
    have heq : -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1))
        = -(f' x / (f x) ^ 2 - A * x ^ (-α - 1)) := by
      rw [← hAα]
      field_simp
      ring
    rw [heq]
    linarith
  -- hence `H` is antitone on `[r₀, ∞)`
  have hanti : AntitoneOn H (Ici r₀) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici r₀) ?_ ?_ ?_
    · -- continuity of `H` on `[r₀, ∞)`
      intro x hx
      rw [mem_Ici] at hx
      rcases eq_or_lt_of_le hx with hx' | hx'
      · subst hx'
        have hfcont : ContinuousAt f r₀ := (hderiv r₀ le_rfl).continuousAt
        have h1 : ContinuousAt (fun y => (f y)⁻¹) r₀ :=
          hfcont.inv₀ (ne_of_gt (hpos r₀ le_rfl))
        have h2 : ContinuousAt (fun y : ℝ => (A / α) * y ^ (-α)) r₀ :=
          (Real.continuousAt_rpow_const r₀ (-α) (Or.inl (ne_of_gt hr₀))).const_mul (A / α)
        exact (h1.sub h2).continuousWithinAt
      · exact (hHderiv x hx').differentiableAt.continuousAt.continuousWithinAt
    · -- differentiability on the interior
      intro x hx
      rw [interior_Ici] at hx
      exact (hHderiv x hx).differentiableAt.differentiableWithinAt
    · -- derivative sign
      intro x hx
      rw [interior_Ici] at hx
      rw [(hHderiv x hx).deriv]
      exact hHnonpos x hx
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  -- `H r ≥ H R ≥ -(A/α) R^{-α}` for all `R ≥ r`, hence `H r ≥ 0`
  have hkey : 0 ≤ H r := by
    have hmono : ∀ R, r ≤ R → H R ≤ H r := fun R hR =>
      hanti (mem_Ici.2 (le_trans hr le_rfl)) (mem_Ici.2 (le_trans hr hR)) hR
    have hlow : ∀ R, r ≤ R → -((A / α) * R ^ (-α)) ≤ H r := by
      intro R hR
      have hRpos : 0 < R := lt_of_lt_of_le hrpos hR
      have h1 : (0 : ℝ) ≤ (f R)⁻¹ := inv_nonneg.2 (le_of_lt (hpos R (le_trans hr hR)))
      have h2 : (f R)⁻¹ - (A / α) * R ^ (-α) ≤ H r := hmono R hR
      linarith
    have htend : Tendsto (fun R : ℝ => -((A / α) * R ^ (-α))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
      simpa using (h0.const_mul (A / α)).neg
    exact le_of_tendsto htend (eventually_atTop.2 ⟨r, hlow⟩)
  -- conclude
  have hfr : 0 < f r := hpos r hr
  have hH' : (A / α) * r ^ (-α) ≤ (f r)⁻¹ := by
    have := hkey
    simp only [hH] at this
    linarith
  have h1 : (A / α) * r ^ (-α) * f r ≤ 1 := by
    have h2 := mul_le_mul_of_nonneg_right hH' (le_of_lt hfr)
    rwa [inv_mul_cancel₀ (ne_of_gt hfr)] at h2
  have h2 : f r ≤ 1 / ((A / α) * r ^ (-α)) := by
    rw [le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using h1
  have h3 : 1 / ((A / α) * r ^ (-α)) = α / A * r ^ α := by
    rw [Real.rpow_neg hrpos.le, one_div, mul_inv]
    field_simp
  linarith [h2, h3.le, h3.symm.le]

open Filter Set MeasureTheory
open scoped Topology


/-- **Lemma I.4.5(2)** without a continuity hypothesis on `f'`. -/
theorem lemma_I_4_5_two_nocont {f f' : ℝ → ℝ} {A α r₀ : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ x, r₀ ≤ x → HasDerivAt f (f' x) x)
    (hpos : ∀ x, r₀ ≤ x → 0 < f x)
    (hinf : Tendsto f atTop atTop)
    (hineq : ∀ x, r₀ ≤ x → f' x ≤ A * x ^ (-α - 1) * (f x) ^ 2) :
    ∀ r, r₀ ≤ r → α / A * r ^ α ≤ f r := by
  set H : ℝ → ℝ := fun x => (f x)⁻¹ - (A / α) * x ^ (-α) with hH
  have hHderiv : ∀ x, r₀ < x →
      HasDerivAt H (-(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1))) x := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hxpos : 0 < x := lt_of_lt_of_le hr₀ hxr
    have h1 : HasDerivAt (fun y => (f y)⁻¹) (-(f' x / (f x) ^ 2)) x := by
      have h := (hderiv x hxr).inv (ne_of_gt (hpos x hxr))
      rwa [neg_div] at h
    have h2 : HasDerivAt (fun y => (A / α) * y ^ (-α))
        ((A / α) * (-α * x ^ (-α - 1))) x :=
      (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hxpos))).const_mul (A / α)
    exact h1.sub h2
  have hHnonneg : ∀ x, r₀ < x →
      0 ≤ -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1)) := by
    intro x hx
    have hxr : r₀ ≤ x := le_of_lt hx
    have hfpos : 0 < f x := hpos x hxr
    have hsq : 0 < (f x) ^ 2 := by positivity
    have hineq' : f' x / (f x) ^ 2 ≤ A * x ^ (-α - 1) := by
      rw [div_le_iff₀ hsq]
      exact hineq x hxr
    have hAα : A / α * α = A := by field_simp
    have heq : -(f' x / (f x) ^ 2) - (A / α) * (-α * x ^ (-α - 1)) =
        A * x ^ (-α - 1) - f' x / (f x) ^ 2 := by
      rw [← hAα]
      field_simp
      ring
    rw [heq]
    linarith
  have hmonoOn : MonotoneOn H (Ici r₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici r₀) ?_ ?_ ?_
    · intro x hx
      rw [mem_Ici] at hx
      rcases eq_or_lt_of_le hx with hx' | hx'
      · subst hx'
        have hfcont : ContinuousAt f r₀ := (hderiv r₀ le_rfl).continuousAt
        have h1 : ContinuousAt (fun y => (f y)⁻¹) r₀ :=
          hfcont.inv₀ (ne_of_gt (hpos r₀ le_rfl))
        have h2 : ContinuousAt (fun y : ℝ => (A / α) * y ^ (-α)) r₀ :=
          (Real.continuousAt_rpow_const r₀ (-α) (Or.inl (ne_of_gt hr₀))).const_mul (A / α)
        exact (h1.sub h2).continuousWithinAt
      · exact (hHderiv x hx').differentiableAt.continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hHderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hHderiv x hx).deriv]
      exact hHnonneg x hx
  intro r hr
  have hrpos : 0 < r := lt_of_lt_of_le hr₀ hr
  have hkey : H r ≤ 0 := by
    have hmono : ∀ R, r ≤ R → H r ≤ H R := fun R hR =>
      hmonoOn (mem_Ici.2 (le_trans hr le_rfl)) (mem_Ici.2 (le_trans hr hR)) hR
    have htend : Tendsto H atTop (𝓝 0) := by
      have hinv : Tendsto (fun R : ℝ => (f R)⁻¹) atTop (𝓝 0) := hinf.inv_tendsto_atTop
      have hpow : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
      have hlim := hinv.sub (hpow.const_mul (A / α))
      simpa only [hH, mul_zero, sub_zero] using hlim
    exact ge_of_tendsto htend (eventually_atTop.2 ⟨r, hmono⟩)
  have hfr : 0 < f r := hpos r hr
  have hbound : (f r)⁻¹ ≤ (A / α) * r ^ (-α) := by
    have h := hkey
    simp only [hH] at h
    linarith
  have hposB : 0 < (A / α) * r ^ (-α) := by positivity
  have hinv := (inv_le_comm₀ hfr hposB).mp hbound
  have heq : ((A / α) * r ^ (-α))⁻¹ = α / A * r ^ α := by
    rw [Real.rpow_neg hrpos.le, mul_inv, inv_inv]
    field_simp
  exact heq ▸ hinv

open Filter Set MeasureTheory
open scoped Topology


/-- `s ↦ h s * s ^ (-α-1)` is integrable on `Ioi r` for `r > 0`, `α > 0`, `h`
measurable and bounded on `[r,∞)`. -/
theorem integrableOn_mul_rpow_neg {h : ℝ → ℝ} {α r C : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hmeas : Measurable h) (hC : ∀ t, r ≤ t → |h t| ≤ C) :
    IntegrableOn (fun s => h s * s ^ (-α - 1)) (Ioi r) := by
  have hbound : IntegrableOn (fun s => |C| * s ^ (-α - 1)) (Ioi r) := by
    have h1 : IntegrableOn (fun s : ℝ => s ^ (-α - 1)) (Ioi r) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -α - 1 < -1) hr
    exact h1.const_mul _
  refine Integrable.mono hbound ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_of_lt_of_le hr hs.le
    have hCs : |h s| ≤ |C| := le_trans (hC s hs.le) (le_abs_self C)
    have hpos : 0 ≤ s ^ (-α - 1) := Real.rpow_nonneg hs0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg C) hpos)]
    exact mul_le_mul_of_nonneg_right hCs hpos

/-- Finite-`R` form of the integral identity: for `r₀ ≤ r ≤ R`,
`1/f r = 1/f R + (A/α)(r^{-α} - R^{-α}) - A ∫_r^R h s s^{-α-1} ds`. -/
theorem inv_eq_of_ode {f f' h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    {r R : ℝ} (hr : r₀ ≤ r) (hrR : r ≤ R) :
    (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, h s * s ^ (-α - 1) := by
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR
  have hsub : uIcc r R ⊆ Ici r₀ := by
    rw [uIcc_of_le hrR]; exact fun x hx => le_trans hr hx.1
  have hp : ∀ t, r ≤ t → |A * (1 - h t) * t ^ (-α - 1)| ≤ A * (1 + |C|) * r ^ (-α - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hr0 ht
    have hpow : t ^ (-α - 1) ≤ r ^ (-α - 1) :=
      Real.rpow_le_rpow_of_nonpos hr0 ht (by linarith : -α - 1 ≤ 0)
    have hpow0 : 0 ≤ t ^ (-α - 1) := Real.rpow_nonneg ht0.le _
    have h2 : |1 - h t| ≤ 1 + |C| := by
      have hCt : |h t| ≤ |C| := le_trans (hC t (le_trans hr ht)) (le_abs_self C)
      have habs := abs_sub (1 : ℝ) (h t); rw [abs_one] at habs; linarith
    have h4 : |1 - h t| * t ^ (-α - 1) ≤ (1 + |C|) * r ^ (-α - 1) :=
      mul_le_mul h2 hpow hpow0 (by positivity)
    rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hpow0]
    calc A * |1 - h t| * t ^ (-α - 1) = A * (|1 - h t| * t ^ (-α - 1)) := by ring
      _ ≤ A * ((1 + |C|) * r ^ (-α - 1)) := mul_le_mul_of_nonneg_left h4 hA.le
      _ = A * (1 + |C|) * r ^ (-α - 1) := by ring
  have hInt_f : IntervalIntegrable (fun t => f' t / (f t) ^ 2) volume r R := by
    have hb : IntervalIntegrable (fun t => A * (1 - h t) * t ^ (-α - 1)) volume r R := by
      refine intervalIntegrable_of_bound (C := A * (1 + |C|) * r ^ (-α - 1)) ?_ ?_
      · fun_prop
      · filter_upwards [ae_restrict_mem measurableSet_uIcc] with t ht
        rw [uIcc_of_le hrR] at ht
        rw [Real.norm_eq_abs]
        exact hp t ht.1
    refine hb.congr (fun t ht => ?_)
    rw [uIoc_of_le hrR] at ht
    have htr : r₀ ≤ t := le_trans hr ht.1.le
    have hft : f t ≠ 0 := ne_of_gt (hpos t htr)
    rw [hode t htr]
    field_simp
  have hderivinv : ∀ t ∈ uIcc r R, HasDerivAt (fun u => -(f u)⁻¹) (f' t / (f t) ^ 2) t := by
    intro t ht
    have h1 := ((hderiv t (hsub ht)).inv (ne_of_gt (hpos t (hsub ht)))).neg
    refine h1.congr_deriv ?_
    ring
  have hFTC : ∫ t in r..R, f' t / (f t) ^ 2 = -(f R)⁻¹ + (f r)⁻¹ := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderivinv hInt_f
    rw [h]
    ring
  have hsplit : ∫ t in r..R, f' t / (f t) ^ 2
      = A * (∫ t in r..R, t ^ (-α - 1)) - A * (∫ t in r..R, h t * t ^ (-α - 1)) := by
    have hpt : ∀ t ∈ uIcc r R,
        f' t / (f t) ^ 2 = A * t ^ (-α - 1) - A * (h t * t ^ (-α - 1)) := by
      intro t ht
      rw [uIcc_of_le hrR] at ht
      have htr : r₀ ≤ t := le_trans hr ht.1
      have hft : f t ≠ 0 := ne_of_gt (hpos t htr)
      rw [hode t htr]
      field_simp
    have hint1 : IntervalIntegrable (fun t => A * t ^ (-α - 1)) volume r R := by
      refine intervalIntegrable_of_bound (C := A * r ^ (-α - 1)) ?_ ?_
      · fun_prop
      · filter_upwards [ae_restrict_mem measurableSet_uIcc] with t ht
        rw [uIcc_of_le hrR] at ht
        have ht0 : 0 < t := lt_of_lt_of_le hr0 ht.1
        have hpow : t ^ (-α - 1) ≤ r ^ (-α - 1) :=
          Real.rpow_le_rpow_of_nonpos hr0 ht.1 (by linarith : -α - 1 ≤ 0)
        have hpow0 : 0 ≤ t ^ (-α - 1) := Real.rpow_nonneg ht0.le _
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hA, abs_of_nonneg hpow0]
        exact mul_le_mul_of_nonneg_left hpow hA.le
    have hint2 : IntervalIntegrable (fun t => A * (h t * t ^ (-α - 1))) volume r R := by
      refine intervalIntegrable_of_bound (C := A * (|C| * r ^ (-α - 1))) ?_ ?_
      · fun_prop
      · filter_upwards [ae_restrict_mem measurableSet_uIcc] with t ht
        rw [uIcc_of_le hrR] at ht
        have ht0 : 0 < t := lt_of_lt_of_le hr0 ht.1
        have hpow : t ^ (-α - 1) ≤ r ^ (-α - 1) :=
          Real.rpow_le_rpow_of_nonpos hr0 ht.1 (by linarith : -α - 1 ≤ 0)
        have hpow0 : 0 ≤ t ^ (-α - 1) := Real.rpow_nonneg ht0.le _
        have hCt : |h t| ≤ |C| := le_trans (hC t (le_trans hr ht.1)) (le_abs_self C)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hA, abs_mul, abs_of_nonneg hpow0]
        have h2 : |h t| * t ^ (-α - 1) ≤ |C| * r ^ (-α - 1) :=
          mul_le_mul hCt hpow hpow0 (abs_nonneg C)
        calc A * (|h t| * t ^ (-α - 1)) ≤ A * (|C| * r ^ (-α - 1)) :=
              mul_le_mul_of_nonneg_left h2 hA.le
          _ = A * (|C| * r ^ (-α - 1)) := rfl
    rw [intervalIntegral.integral_congr hpt,
      intervalIntegral.integral_sub hint1 hint2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hrpow : ∫ t in r..R, t ^ (-α - 1) = (r ^ (-α) - R ^ (-α)) / α := by
    have hzero : (0:ℝ) ∉ uIcc r R := by
      rw [uIcc_of_le hrR]
      exact fun hmem => (not_le.2 hr0) hmem.1
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩)]
    have h1 : -α - 1 + 1 = -α := by ring
    rw [h1]
    field_simp
    ring
  calc (f r)⁻¹ = (f R)⁻¹ + ∫ t in r..R, f' t / (f t) ^ 2 := by rw [hFTC]; ring
    _ = (f R)⁻¹ + (A * (∫ t in r..R, t ^ (-α - 1))
          - A * (∫ t in r..R, h t * t ^ (-α - 1))) := by rw [hsplit]
    _ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α))
          - A * ∫ s in r..R, h s * s ^ (-α - 1) := by
        rw [hrpow]; ring

/-- **Lemma I.4.5(3)**. -/
theorem lemma_I_4_5_three {f f' h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C) :
    ∀ r, r₀ ≤ r →
      f r = (α / A) * r ^ α / (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) := by
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  set I : ℝ := ∫ s in Ioi r, h s * s ^ (-α - 1) with hIdef
  have hIint : IntegrableOn (fun s => h s * s ^ (-α - 1)) (Ioi r) :=
    integrableOn_mul_rpow_neg hr0 hα hmeas (fun t ht => hC t (le_trans hr ht))
  have hlim : Tendsto (fun R : ℝ =>
      (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, h s * s ^ (-α - 1))
      atTop (𝓝 (A / α * r ^ (-α) - A * I)) := by
    have h1 : Tendsto (fun R : ℝ => (f R)⁻¹) atTop (𝓝 0) := hinf.inv_tendsto_atTop
    have h2 : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
    have h3 : Tendsto (fun R : ℝ => A / α * (r ^ (-α) - R ^ (-α))) atTop (𝓝 (A / α * r ^ (-α))) := by
      have h0 : Tendsto (fun _ : ℝ => r ^ (-α)) atTop (𝓝 (r ^ (-α))) := tendsto_const_nhds
      have h := (h0.sub h2).const_mul (A / α)
      simpa using h
    have h4 : Tendsto (fun R : ℝ => A * ∫ s in r..R, h s * s ^ (-α - 1)) atTop (𝓝 (A * I)) := by
      have h := (intervalIntegral_tendsto_integral_Ioi r hIint tendsto_id).const_mul A
      simpa [hIdef] using h
    have h5 := (h1.add h3).sub h4
    simpa using h5
  have hkey : (f r)⁻¹ = A / α * r ^ (-α) - A * I := by
    have hconst : Tendsto (fun _ : ℝ => (f r)⁻¹) atTop (𝓝 ((f r)⁻¹)) := tendsto_const_nhds
    have hfin : ∀ᶠ R in atTop, (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α))
        - A * ∫ s in r..R, h s * s ^ (-α - 1) := by
      filter_upwards [eventually_ge_atTop r] with R hR
      exact inv_eq_of_ode hA hα hr₀ hderiv hpos hode hmeas hC hr hR
    exact tendsto_nhds_unique (hconst.congr' hfin) hlim
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  have hrmα : r ^ (-α) = (r ^ α)⁻¹ := Real.rpow_neg hr0.le α
  have hfr : 0 < f r := hpos r hr
  have hden : 1 - α * r ^ α * I = (α / A) * r ^ α * (f r)⁻¹ := by
    rw [hkey, hrmα]
    field_simp
  have hdenpos : 0 < 1 - α * r ^ α * I := by
    rw [hden]
    positivity
  have hfrne : f r ≠ 0 := ne_of_gt hfr
  have hdenne : 1 - α * r ^ α * I ≠ 0 := ne_of_gt hdenpos
  rw [hden]
  field_simp

end PercLib.CriticalLRP
