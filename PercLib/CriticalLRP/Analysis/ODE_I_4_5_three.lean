/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I*, Lemma I.4.5 (p. 35), part 3.

Paper statement: "If `f (r) → ∞` as `r → ∞` and `f'(r) = A(1 - h(r)) r^{-α-1} f(r)^2`
for some bounded measurable `h : (0,∞) → ℝ` then
`f(r) = (α/A) r^α (1 - α r^α ∫_r^∞ h(s) s^{-α-1} ds)^{-1}`
for every `r > 0`."

Comments on the statement as formalized:
* the identity can only hold for those `r` on which the differential equation is
  assumed (the paper's `r ≥ r₀`); we state it for `r ≥ r₀`;
* `h` is only assumed measurable and bounded on `[r₀,∞)`, exactly what is needed
  for the improper integral `∫_r^∞ h(s) s^{-α-1} ds` to exist.

Proof (the paper's): `(1/f)' = -f'/f² = -A(1-h(r)) r^{-α-1}`; integrate from `r`
to `R`, let `R → ∞`, and use `f → ∞` so that `1/f(R) → 0` and `R^{-α} → 0`.
-/
module

public import PercLib.CriticalLRP.Analysis.RegularVariation

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

end PercLib.CriticalLRP.Analysis
