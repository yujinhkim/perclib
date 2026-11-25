/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0 license.

# Corner-safe first-moment ODE handoff (Proposition I.4.2 / Lemma I.4.5)

Source: Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.5 (p. 35) and its use in (I.4.6)-(I.4.7) (pp. 35-36).

## Why this file

The paper's Lemma I.4.5 is stated for `f : (0,∞) -> (0,∞)` *differentiable*, and the
display (I.4.6) is the differential equation

  `d/dr E_{b_c,r}|K| = (1 - Ebar_{1,r}) * b_c * r^(-a-1) * (E_{b_c,r}|K|)^2`.

The function to which it is applied is the cut-off cluster mass `r |-> E_{b_c,r}|K|`.
The cut-off profile is `J_r(s) = K s - K r` for `s <= r` and `0` for `s > r`; at
`r = s` it has a genuine corner.  `PercLib.CriticalLRP.FiniteVolume.not_hasDerivAt_cutoffProfile`
*proves* that the two-sided `r`-derivative fails there (left derivative `0`, right
derivative `|J'(s)|`), and `hasDerivWithinAt_cutoffProfile_Iic` /
`hasDerivWithinAt_cutoffProfile_Ioi` identify the two one-sided derivatives.  The
exceptional set is the set of edge lengths of the lattice, which is countable.

Hence the hypothesis actually available for (I.4.6) is never
`forall t >= r0, HasDerivAt f (f' t) t`: it is

* absolute continuity of `f` on every `[r0, R]` (the cut-off mass is a monotone limit
  of finite-volume masses, each `C^1` off the corner set and continuous at it), and
* the differential equation only at almost every `r` (the corner set is null).

The declarations below prove Lemma I.4.5(3), the exact identity (I.4.7), the
asymptotic of Proposition I.4.2 and the logarithmic-integrability statement *from
exactly that weaker, corner-safe hypothesis*, so that the handoff
`(I.4.5) => (I.4.6) => (I.4.7)` is available for the real model rather than only for
a hypothetical everywhere-differentiable `chi`.

`ae_hasDerivAt_of_countable_not` and `ae_restrict_hasDerivAt_of_countable_not` record
the step that converts the corner structure into the a.e. hypothesis: a derivative
that exists off a countable set exists almost everywhere.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.Asymptotic
public import PercLib.CriticalLRP.Analysis.ErrorFunctions
public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.Analysis.Lemma_I_4_13
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.LogIntegrability

/-! # The first-moment ODE with absolute continuity and an almost-everywhere derivative -/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.CornerSafe

/-! ## The corner structure only loses a null set -/

/-- **Corner bookkeeping.** A function differentiable with derivative `f'` off a
countable set is differentiable with derivative `f'` almost everywhere.  In the
application `S` is the set of edge lengths where the cut-off profile has its corner,
and `CutoffCorner.not_hasDerivAt_cutoffProfile` shows differentiability genuinely
fails there. -/
theorem ae_hasDerivAt_of_countable_not {f f' : ℝ → ℝ} {S : Set ℝ} (hS : S.Countable)
    (h : ∀ t, t ∉ S → HasDerivAt f (f' t) t) :
    ∀ᵐ t ∂(volume : Measure ℝ), HasDerivAt f (f' t) t := by
  have hzero : (volume : Measure ℝ) S = 0 := hS.measure_zero volume
  have hcompl : Sᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 hzero
  filter_upwards [hcompl] with t ht
  exact h t ht

/-- The restricted form used as the hypothesis of the corner-safe Lemma I.4.5. -/
theorem ae_restrict_hasDerivAt_of_countable_not {f f' : ℝ → ℝ} {S s : Set ℝ}
    (hS : S.Countable) (h : ∀ t, t ∉ S → HasDerivAt f (f' t) t) :
    ∀ᵐ t ∂(volume.restrict s), HasDerivAt f (f' t) t :=
  ae_restrict_of_ae (ae_hasDerivAt_of_countable_not hS h)

/-! ## Absolute continuity of the reciprocal -/

/-- On `[c, ∞)` with `c > 0`, inversion is `c⁻²`-Lipschitz. -/
theorem lipschitzOnWith_inv_Ici {c : ℝ} (hc : 0 < c) :
    LipschitzOnWith ⟨c⁻¹ ^ 2, by positivity⟩ (fun x : ℝ => x⁻¹) (Set.Ici c) := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  have hx0 : 0 < x := lt_of_lt_of_le hc hx
  have hy0 : 0 < y := lt_of_lt_of_le hc hy
  have hxy : c * c ≤ x * y := mul_le_mul hx hy hc.le hx0.le
  have hK : (1 : ℝ) / (x * y) ≤ c⁻¹ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (c⁻¹ : ℝ) ^ 2 * (c * c) = 1 := by
      have h1 : (c⁻¹ : ℝ) * c = 1 := inv_mul_cancel₀ (ne_of_gt hc)
      calc (c⁻¹ : ℝ) ^ 2 * (c * c) = ((c⁻¹ : ℝ) * c) * ((c⁻¹ : ℝ) * c) := by ring
        _ = 1 := by rw [h1]; ring
    calc (1 : ℝ) = (c⁻¹ : ℝ) ^ 2 * (c * c) := h2.symm
      _ ≤ (c⁻¹ : ℝ) ^ 2 * (x * y) := mul_le_mul_of_nonneg_left hxy (sq_nonneg _)
  have hgoal : |x⁻¹ - y⁻¹| ≤ (c⁻¹ : ℝ) ^ 2 * |x - y| := by
    rw [inv_sub_inv (ne_of_gt hx0) (ne_of_gt hy0), abs_div, abs_mul, abs_of_pos hx0,
      abs_of_pos hy0, abs_sub_comm]
    calc |x - y| / (x * y) = |x - y| * (1 / (x * y)) := by ring
      _ ≤ |x - y| * (c⁻¹ : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hK (abs_nonneg _)
      _ = (c⁻¹ : ℝ) ^ 2 * |x - y| := by ring
  rw [Real.dist_eq, Real.dist_eq]
  exact hgoal

/-- The reciprocal of a positive absolutely continuous function is absolutely
continuous. -/
theorem absolutelyContinuousOnInterval_inv {f : ℝ → ℝ} {a b c : ℝ}
    (hac : AbsolutelyContinuousOnInterval f a b) (hc : 0 < c)
    (hcf : ∀ t ∈ uIcc a b, c ≤ f t) :
    AbsolutelyContinuousOnInterval (fun t => (f t)⁻¹) a b := by
  have hmaps : MapsTo f (uIcc a b) (Set.Ici c) := fun t ht => hcf t ht
  exact (lipschitzOnWith_inv_Ici hc).comp_absolutelyContinuousOnInterval hmaps hac

/-! ## Lemma I.4.5(3) with an almost-everywhere derivative -/

/-- **Finite-`R` integral identity with an a.e. derivative** (corner-safe form of the
computation inside Lemma I.4.5): for `r0 <= r <= R`,

`1/f r = 1/f R + (A/a)(r^(-a) - R^(-a)) - A * int_r^R h s s^(-a-1) ds`,

assuming only absolute continuity of `f` on every `[r0, R]`, positivity of `f` on
`[r0, ∞)`, and the differential equation a.e. -/
theorem inv_eq_of_ode_ae {f h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    {r R : ℝ} (hr : r₀ ≤ r) (hrR : r ≤ R) :
    (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α))
      - A * ∫ s in r..R, h s * s ^ (-α - 1) := by
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR
  have hr₀R : r₀ ≤ R := le_trans hr hrR
  have hsub : uIcc r R ⊆ Ici r₀ := by
    rw [uIcc_of_le hrR]
    exact fun x hx => le_trans hr hx.1
  -- corner bookkeeping: the a.e. hypothesis, unfolded
  have hae' : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ Ici r₀ → HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t :=
    (ae_restrict_iff' measurableSet_Ici).1 hae
  -- absolute continuity on `[r, R]`
  have hacR : AbsolutelyContinuousOnInterval f r R := by
    refine (hac R hr₀R).mono ?_
    rw [uIcc_of_le hr₀R, uIcc_of_le hrR]
    exact Icc_subset_Icc hr le_rfl
  -- a uniform positive lower bound for `f` on `[r, R]`
  obtain ⟨x₀, hx₀, hmin⟩ :=
    isCompact_uIcc.exists_isMinOn ⟨r, left_mem_uIcc⟩ hacR.continuousOn
  have hc : 0 < f x₀ := hpos x₀ (hsub hx₀)
  have hcf : ∀ t ∈ uIcc r R, f x₀ ≤ f t := fun t ht => hmin ht
  have hgac : AbsolutelyContinuousOnInterval (fun t => (f t)⁻¹) r R :=
    absolutelyContinuousOnInterval_inv hacR hc hcf
  have hFTC : ∫ t in r..R, deriv (fun u => (f u)⁻¹) t = (f R)⁻¹ - (f r)⁻¹ :=
    hgac.integral_deriv_eq_sub
  -- the derivative of the reciprocal, a.e. on `(r, R)`
  have hderivae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc r R →
      deriv (fun u => (f u)⁻¹) t = -(A * (1 - h t) * t ^ (-α - 1)) := by
    filter_upwards [hae'] with t ht htu
    have htI : t ∈ Ici r₀ := hsub (uIoc_subset_uIcc htu)
    have hft : f t ≠ 0 := ne_of_gt (hpos t htI)
    have hval : -(A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) / (f t) ^ 2
        = -(A * (1 - h t) * t ^ (-α - 1)) := by
      field_simp
    rw [← hval]
    exact ((ht htI).inv hft).deriv
  have hInt : ∫ t in r..R, deriv (fun u => (f u)⁻¹) t
      = -(∫ t in r..R, A * (1 - h t) * t ^ (-α - 1)) := by
    rw [intervalIntegral.integral_congr_ae hderivae, intervalIntegral.integral_neg]
  -- boundedness of the integrand on `[r, R]`
  have hint1 : IntervalIntegrable (fun t => A * t ^ (-α - 1)) volume r R := by
    refine PercLib.CriticalLRP.Analysis.intervalIntegrable_of_bound (C := A * r ^ (-α - 1)) ?_ ?_
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
    refine PercLib.CriticalLRP.Analysis.intervalIntegrable_of_bound
      (C := A * (|C| * r ^ (-α - 1))) ?_ ?_
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
  have hsplit : ∫ t in r..R, A * (1 - h t) * t ^ (-α - 1)
      = A * (∫ t in r..R, t ^ (-α - 1)) - A * (∫ t in r..R, h t * t ^ (-α - 1)) := by
    have hpt : ∀ t ∈ uIcc r R, A * (1 - h t) * t ^ (-α - 1)
        = A * t ^ (-α - 1) - A * (h t * t ^ (-α - 1)) := by
      intro t _
      ring
    rw [intervalIntegral.integral_congr hpt,
      intervalIntegral.integral_sub hint1 hint2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hrpow : ∫ t in r..R, t ^ (-α - 1) = (r ^ (-α) - R ^ (-α)) / α := by
    have hzero : (0 : ℝ) ∉ uIcc r R := by
      rw [uIcc_of_le hrR]
      exact fun hmem => (not_le.2 hr0) hmem.1
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩)]
    have h1 : -α - 1 + 1 = -α := by ring
    rw [h1]
    field_simp
    ring
  have hkey : (f R)⁻¹ - (f r)⁻¹
      = -(A * ∫ t in r..R, t ^ (-α - 1)) + A * ∫ t in r..R, h t * t ^ (-α - 1) := by
    rw [← hFTC, hInt, hsplit]
    ring
  calc (f r)⁻¹ = (f R)⁻¹ - ((f R)⁻¹ - (f r)⁻¹) := by ring
    _ = (f R)⁻¹ - (-(A * ∫ t in r..R, t ^ (-α - 1))
          + A * ∫ t in r..R, h t * t ^ (-α - 1)) := by rw [hkey]
    _ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α))
          - A * ∫ s in r..R, h s * s ^ (-α - 1) := by
        rw [hrpow]; ring

/-- **Lemma I.4.5(3), corner-safe form.** If `f` is positive and absolutely
continuous on every `[r0, R]`, `f -> ∞`, and `f' = A(1 - h) r^(-a-1) f^2` at almost
every `r >= r0`, then

`f r = (a/A) r^a / (1 - a r^a * int_r^∞ h s s^(-a-1) ds)`

for every `r >= r0` -- the display (I.4.7).  The hypothesis that replaces
"`f` is differentiable" is exactly what the cut-off cluster mass supplies: the corner
set of the cut-off profile is countable hence null. -/
theorem lemma_I_4_5_three_ae {f h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C) :
    ∀ r, r₀ ≤ r →
      f r = (α / A) * r ^ α / (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) := by
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  set I : ℝ := ∫ s in Ioi r, h s * s ^ (-α - 1) with hIdef
  have hIint : IntegrableOn (fun s => h s * s ^ (-α - 1)) (Ioi r) :=
    PercLib.CriticalLRP.Analysis.integrableOn_mul_rpow_neg hr0 hα hmeas
      (fun t ht => hC t (le_trans hr ht))
  have hlim : Tendsto (fun R : ℝ =>
      (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α)) - A * ∫ s in r..R, h s * s ^ (-α - 1))
      atTop (𝓝 (A / α * r ^ (-α) - A * I)) := by
    have h1 : Tendsto (fun R : ℝ => (f R)⁻¹) atTop (𝓝 0) := hinf.inv_tendsto_atTop
    have h2 : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
    have h3 : Tendsto (fun R : ℝ => A / α * (r ^ (-α) - R ^ (-α))) atTop
        (𝓝 (A / α * r ^ (-α))) := by
      have h0 : Tendsto (fun _ : ℝ => r ^ (-α)) atTop (𝓝 (r ^ (-α))) := tendsto_const_nhds
      have h := (h0.sub h2).const_mul (A / α)
      simpa using h
    have h4 : Tendsto (fun R : ℝ => A * ∫ s in r..R, h s * s ^ (-α - 1)) atTop
        (𝓝 (A * I)) := by
      have h := (intervalIntegral_tendsto_integral_Ioi r hIint tendsto_id).const_mul A
      simpa [hIdef] using h
    have h5 := (h1.add h3).sub h4
    simpa using h5
  have hkey : (f r)⁻¹ = A / α * r ^ (-α) - A * I := by
    have hconst : Tendsto (fun _ : ℝ => (f r)⁻¹) atTop (𝓝 ((f r)⁻¹)) :=
      tendsto_const_nhds
    have hfin : ∀ᶠ R in atTop, (f r)⁻¹ = (f R)⁻¹ + A / α * (r ^ (-α) - R ^ (-α))
        - A * ∫ s in r..R, h s * s ^ (-α - 1) := by
      filter_upwards [eventually_ge_atTop r] with R hR
      exact inv_eq_of_ode_ae hA hα hr₀ hac hpos hae hmeas hC hr hR
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

/-! ## The resulting error identity, asymptotic and log-integrability -/

/-- Corner-safe form of the error identity: on `[r0, ∞)`,
`1 + H_r = (1 - a r^a * int_r^∞ h s s^(-a-1) ds)^(-1)` for
`H_r = (A/a) r^(-a) f r - 1`. -/
theorem one_add_error_eq_ae {f h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C) :
    ∀ r, r₀ ≤ r →
      1 + (A / α * r ^ (-α) * f r - 1)
        = (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))⁻¹ := by
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hform := lemma_I_4_5_three_ae hA hα hr₀ hac hpos hinf hae hmeas hC r hr
  set I : ℝ := ∫ s in Ioi r, h s * s ^ (-α - 1) with hI
  have hrr : r ^ (-α) * r ^ α = 1 := by
    rw [← Real.rpow_add hr0]
    norm_num
  have hAne : A ≠ 0 := ne_of_gt hA
  have hαne : α ≠ 0 := ne_of_gt hα
  have hdenne : 1 - α * r ^ α * I ≠ 0 := by
    intro hc
    rw [hc] at hform
    simp at hform
    linarith [hpos r hr]
  rw [hform]
  have h1 : A / α * r ^ (-α) * (α / A * r ^ α / (1 - α * r ^ α * I))
      = (r ^ (-α) * r ^ α) * (1 - α * r ^ α * I)⁻¹ := by
    field_simp
  rw [h1, hrr, one_mul]
  ring

/-- **Proposition I.4.2, analytic core, corner-safe form**: if the multiplicative
error `h` of (I.4.6) tends to `0`, then `f r / ((a/A) r^a) -> 1`.  Only an a.e.
differential equation and absolute continuity are assumed. -/
theorem first_moment_asymptotic_ae {f h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun r => f r / (α / A * r ^ α)) atTop (𝓝 1) := by
  have hw : Tendsto (fun r : ℝ => r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) atTop (𝓝 0) :=
    PercLib.CriticalLRP.VolumeMoments.FirstMoment.tendsto_rpow_mul_integral_Ioi hα hmeas h0
  have hden : Tendsto (fun r : ℝ => 1 - α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun r : ℝ => α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)))
        atTop (𝓝 0) := by simpa using hw.const_mul α
    simpa using tendsto_const_nhds.sub h1
  have hinv : Tendsto
      (fun r : ℝ => (1 - α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)))⁻¹) atTop
        (𝓝 1) := by
    simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  refine hinv.congr' ?_
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hform := lemma_I_4_5_three_ae hA hα hr₀ hac hpos hinf hae hmeas hC r hr
  set I : ℝ := ∫ s in Ioi r, h s * s ^ (-α - 1) with hI
  have hcoe : 0 < α / A * r ^ α := by
    have h2 : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
    positivity
  have hcoene : α / A * r ^ α ≠ 0 := ne_of_gt hcoe
  have hdenne : 1 - α * r ^ α * I ≠ 0 := by
    intro hc
    rw [hc] at hform
    simp at hform
    linarith [hpos r hr]
  rw [hform]
  field_simp

/-- **Lemma I.4.13 (first clause) applied to the first-moment error, corner-safe
form**: if the error profile `h` is a logarithmically integrable error function then
so is `H_r = (A/a) r^(-a) f r - 1`. -/
theorem first_moment_error_logIntegrable_ae {f h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (hlint : PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable h)
    (hHmeas : Measurable (fun r => A / α * r ^ (-α) * f r - 1)) :
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable
      (fun r => A / α * r ^ (-α) * f r - 1) := by
  obtain ⟨-, r₁, hr₁, hint⟩ := hlint
  have hmaj := PercLib.CriticalLRP.VolumeMoments.FirstMoment.integrableOn_hardyUpper
    hα hr₁ hmeas hint
  have hw : Tendsto (fun r : ℝ => r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) atTop (𝓝 0) :=
    PercLib.CriticalLRP.VolumeMoments.FirstMoment.tendsto_rpow_mul_integral_Ioi hα hmeas h0
  have hsmall : ∀ᶠ r : ℝ in atTop,
      |α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))| ≤ 1 / 2 := by
    have h1 : Tendsto (fun r : ℝ => α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)))
        atTop (𝓝 0) := by simpa using hw.const_mul α
    have h2 : Tendsto
        (fun r : ℝ => |α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))|)
        atTop (𝓝 0) := by simpa using h1.abs
    exact h2.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨r₂, hr₂⟩ := eventually_atTop.1 hsmall
  set R : ℝ := max r₀ (max r₁ (max r₂ 1)) with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le hr₀ (le_max_left _ _)
  have hmaj' : IntegrableOn (fun r => r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|)
      (Ioi R) :=
    hmaj.mono_set (Ioi_subset_Ioi (le_trans (le_max_left _ _) (le_max_right _ _)))
  refine ⟨hHmeas, R, hRpos, ?_⟩
  have hmaj2 : IntegrableOn
      (fun r => 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|)) (Ioi R) :=
    hmaj'.const_mul (2 * α)
  refine Integrable.mono hmaj2 (hHmeas.abs.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hrR : R ≤ r := le_of_lt hr
  have hr0 : r₀ ≤ r := le_trans (le_max_left _ _) hrR
  have hs1 : r₂ ≤ max r₂ 1 := le_max_left _ _
  have hs2 : max r₂ 1 ≤ max r₁ (max r₂ 1) := le_max_right _ _
  have hs3 : max r₁ (max r₂ 1) ≤ max r₀ (max r₁ (max r₂ 1)) := le_max_right _ _
  have hs4 : 1 ≤ max r₂ 1 := le_max_right _ _
  have hr2 : r₂ ≤ r := le_trans (le_trans (le_trans hs1 hs2) hs3) hrR
  have hrone : 1 ≤ r := le_trans (le_trans (le_trans hs4 hs2) hs3) hrR
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrone
  set J : ℝ := r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1) with hJ
  have hden_eq : (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) = 1 - α * J := by
    have h1 : α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)
        = α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) := by ring
    rw [h1, ← hJ]
  have hHform : 1 + (A / α * r ^ (-α) * f r - 1) = (1 - α * J)⁻¹ := by
    have h := one_add_error_eq_ae hA hα hr₀ hac hpos hinf hae hmeas hC r hr0
    rw [hden_eq] at h
    exact h
  have hy : A / α * r ^ (-α) * f r = (1 - α * J)⁻¹ := by linarith [hHform]
  have hdenne : 1 - α * J ≠ 0 := by
    intro hc
    rw [hc, inv_zero] at hy
    have h1 : 0 < A / α := by positivity
    have h2 : 0 < r ^ (-α) := Real.rpow_pos_of_pos hrpos _
    have h3 : 0 < f r := hpos r hr0
    have h4 : 0 < A / α * r ^ (-α) * f r := by positivity
    rw [hy] at h4
    exact lt_irrefl 0 h4
  have hHs : (A / α * r ^ (-α) * f r - 1) = α * J / (1 - α * J) := by
    rw [hy]
    field_simp
    ring
  have hsmallJ : |α * J| ≤ 1 / 2 := by
    have h3 := hr₂ r hr2
    simpa [hJ] using h3
  have hIbound : |J| ≤ r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s| := by
    have h1 : |∫ s in Ioi r, h s * s ^ (-α - 1)|
        ≤ ∫ s in Ioi r, |h s * s ^ (-α - 1)| := abs_integral_le_integral_abs
    have h2 : ∫ s in Ioi r, |h s * s ^ (-α - 1)| = ∫ s in Ioi r, s ^ (-α - 1) * |h s| := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := lt_trans hrpos hs
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
      ring
    calc |J| = r ^ α * |∫ s in Ioi r, h s * s ^ (-α - 1)| := by
          rw [hJ, abs_mul, abs_of_nonneg (Real.rpow_nonneg hrpos.le _)]
      _ ≤ r ^ α * ∫ s in Ioi r, |h s * s ^ (-α - 1)| :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hrpos.le _)
      _ = r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s| := by rw [h2]
  have hden_lb : 1 / 2 ≤ |1 - α * J| := by
    have h2 : (1 : ℝ) - |α * J| ≤ |1 - α * J| := by
      have h3 := abs_sub_abs_le_abs_sub (1 : ℝ) (α * J)
      rw [abs_one] at h3
      linarith
    linarith
  have hnum : |α * J / (1 - α * J)| ≤ 2 * α * |J| := by
    rw [abs_div, abs_mul, abs_of_pos hα]
    have h2 : α * |J| / |1 - α * J| ≤ α * |J| / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden_lb
    have h3 : α * |J| / (1 / 2) = 2 * (α * |J|) := by field_simp
    linarith
  have hmain : |A / α * r ^ (-α) * f r - 1| / r
      ≤ 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
    rw [hHs]
    have h1 : |α * J / (1 - α * J)| / r ≤ (2 * α * |J|) / r :=
      div_le_div_of_nonneg_right hnum hrpos.le
    have h2 : (2 * α * |J|) / r
        ≤ 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
      have h3 : 2 * α * |J| / r
          ≤ 2 * α * (r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) / r := by
        gcongr
      have h4 : 2 * α * (r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) / r
          = 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
        have hrr : r ^ α / r = r ^ (α - 1) := (Real.rpow_sub_one hrpos.ne' α).symm
        calc 2 * α * (r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) / r
            = 2 * α * ((r ^ α / r) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
              field_simp
          _ = 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by rw [hrr]
      linarith [h3, le_of_eq h4]
    linarith [h1, h2]
  have hrhs_nn : 0 ≤ 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
    have h1 : 0 ≤ ∫ s in Ioi r, s ^ (-α - 1) * |h s| := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := lt_trans hrpos hs
      positivity
    have h2 : 0 ≤ r ^ (α - 1) := Real.rpow_nonneg hrpos.le _
    have h4 : 0 ≤ r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s| := mul_nonneg h2 h1
    have h5 : 0 ≤ 2 * α := by positivity
    exact mul_nonneg h5 h4
  have h2 : ‖2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|)‖
      = 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hrhs_nn]
  rw [Real.norm_eq_abs, h2, abs_div, abs_of_pos hrpos]
  simpa using hmain

/-! ## The multiplicative error of (I.4.6): bookkeeping of `E0` and `E1`

The right-hand side of (I.4.6) carries the single multiplicative error
`Ebar_1 = 1 - (1 - E_0)(1 - E_1)` of the paper, not `E_1` itself.  The model supplies
`E_0` (from the standing assumption `|J'(r)| = (1 + delta r) r^{-d-a-1}` on the kernel
and Lemma I.4.6) and `E_1` (Lemma I.4.11 + the triangle condition).  To obtain the
second assertion of Proposition I.4.2 one therefore has to show that `Ebar_1` is a
logarithmically integrable error function from the same property of `E_0` and `E_1`.
That transfer is what the next two lemmas do; neither is in the library. -/

/-- Right-multiplication by an eventually bounded measurable function preserves the
log-integrable-error-function property. -/
theorem isLogErrorFunction_mul_right_bounded {f g : ℝ → ℝ}
    (hg : PercLib.CriticalLRP.Analysis.IsLogErrorFunction g) (hfmeas : Measurable f)
    {B r₀ : ℝ} (hB : ∀ r, r₀ ≤ r → |f r| ≤ B) :
    PercLib.CriticalLRP.Analysis.IsLogErrorFunction (fun r => f r * g r) := by
  obtain ⟨⟨hgm, r₁, hr₁, hint⟩, hg0⟩ := hg
  refine ⟨⟨hfmeas.mul hgm, max r₀ r₁, lt_max_of_lt_right hr₁, ?_⟩, ?_⟩
  · have h1 : IntegrableOn (fun r => |g r| / r) (Ioi (max r₀ r₁)) volume :=
      hint.mono_set (Ioi_subset_Ioi (le_max_right _ _))
    have h2 : IntegrableOn (fun r => B * (|g r| / r)) (Ioi (max r₀ r₁)) volume :=
      h1.const_mul B
    refine h2.mono' ((hfmeas.mul hgm).abs.div measurable_id).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [mem_Ioi] at hr
    have hr0 : 0 < r := lt_trans (lt_max_of_lt_right hr₁) hr
    have hbound : |f r| ≤ B := hB r (le_trans (le_max_left _ _) hr.le)
    have hgnn : (0 : ℝ) ≤ |g r| / r := by positivity
    have h1 : ‖|f r * g r| / r‖ = |f r| * (|g r| / r) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_mul]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right hbound hgnn
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun r => B * |g r|) atTop (𝓝 0) := by
      have h := (hg0.norm).const_mul B
      simpa using h
    refine squeeze_zero' ?_ ?_ hb
    · exact .of_forall fun r => norm_nonneg _
    · filter_upwards [eventually_ge_atTop r₀] with r hr
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB r hr) (abs_nonneg _)

/-- The multiplicative error `1 - (1 - E0)(1 - E1)` of (I.4.6) is a logarithmically
integrable error function whenever `E0` and `E1` are, `E0 -> 0` with `|E0| <= 1/8`,
and `0 <= E1 <= B`. -/
theorem isLogErrorFunction_one_sub_mul {E0 E1 : ℝ → ℝ}
    (h0 : PercLib.CriticalLRP.Analysis.IsLogErrorFunction E0)
    (h1 : PercLib.CriticalLRP.Analysis.IsLogErrorFunction E1)
    (h0b : ∀ r, |E0 r| ≤ 1 / 8) (h1nn : ∀ r, 0 ≤ E1 r) {B : ℝ} (hB : ∀ r, E1 r ≤ B) :
    PercLib.CriticalLRP.Analysis.IsLogErrorFunction
      (fun r => 1 - (1 - E0 r) * (1 - E1 r)) := by
  have h0m : Measurable E0 := h0.1.1
  have h1m : Measurable E1 := h1.1.1
  have hsum : PercLib.CriticalLRP.Analysis.IsLogErrorFunction (fun r => E0 r + E1 r) :=
    PercLib.CriticalLRP.Analysis.isLogErrorFunction_add h0 h1
  have hprod : PercLib.CriticalLRP.Analysis.IsLogErrorFunction (fun r => E0 r * E1 r) :=
    isLogErrorFunction_mul_right_bounded (B := max (1 / 8) B) (r₀ := 0) h1 h0m
      (fun r _ => le_trans (h0b r) (le_max_left _ _))
  have hneg : PercLib.CriticalLRP.Analysis.IsLogErrorFunction (fun r => -(E0 r * E1 r)) :=
    PercLib.CriticalLRP.Analysis.isLogErrorFunction_neg hprod
  have hall : PercLib.CriticalLRP.Analysis.IsLogErrorFunction
      (fun r => E0 r + E1 r + -(E0 r * E1 r)) :=
    PercLib.CriticalLRP.Analysis.isLogErrorFunction_add hsum hneg
  refine PercLib.CriticalLRP.Analysis.isLogErrorFunction_congr hall ?_
    (measurable_const.sub ((measurable_const.sub h0m).mul
      (measurable_const.sub h1m)))
  filter_upwards with r
  ring

/-- `=> 0` for the multiplicative error of (I.4.6). -/
theorem tendsto_one_sub_mul {E0 E1 : ℝ → ℝ}
    (h0 : Tendsto E0 atTop (𝓝 0)) (h1 : Tendsto E1 atTop (𝓝 0)) :
    Tendsto (fun r => 1 - (1 - E0 r) * (1 - E1 r)) atTop (𝓝 0) := by
  have hA : Tendsto (fun r => (1 : ℝ) - E0 r) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h0
  have hB : Tendsto (fun r => (1 : ℝ) - E1 r) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h1
  have h := hA.mul hB
  have h' : Tendsto (fun r => 1 - (1 - E0 r) * (1 - E1 r)) atTop
      (𝓝 (1 - (1 - 0) * (1 - 0))) := tendsto_const_nhds.sub h
  simpa using h'

/-- A uniform bound for the multiplicative error of (I.4.6). -/
theorem abs_one_sub_mul_le {E0 E1 : ℝ → ℝ} {B : ℝ}
    (h0b : ∀ r, |E0 r| ≤ 1 / 8) (h1nn : ∀ r, 0 ≤ E1 r) (h1B : ∀ r, E1 r ≤ B) :
    ∀ r, |1 - (1 - E0 r) * (1 - E1 r)| ≤ 1 / 8 + B + (1 / 8) * B := by
  intro r
  have h1 := h0b r
  have h2 := h1nn r
  have h3 := h1B r
  have hB0 : 0 ≤ B := le_trans h2 h3
  have hkey : 1 - (1 - E0 r) * (1 - E1 r) = E0 r + E1 r - E0 r * E1 r := by ring
  rw [hkey]
  have h4 : |E0 r| ≤ 1 / 8 := h1
  have h5 : |E0 r * E1 r| ≤ (1 / 8) * B := by
    rw [abs_mul, abs_of_nonneg h2]
    calc |E0 r| * E1 r ≤ |E0 r| * B := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ ≤ (1 / 8) * B := mul_le_mul_of_nonneg_right h4 hB0
  have h6 : |E0 r + E1 r| ≤ |E0 r| + |E1 r| := abs_add_le _ _
  have h7 : |E1 r| = E1 r := abs_of_nonneg h2
  calc |E0 r + E1 r - E0 r * E1 r| ≤ |E0 r + E1 r| + |E0 r * E1 r| := abs_sub _ _
    _ ≤ (|E0 r| + |E1 r|) + (1 / 8) * B := by linarith [h5, h6]
    _ ≤ (1 / 8 + B) + (1 / 8) * B := by rw [h7]; linarith
    _ = 1 / 8 + B + (1 / 8) * B := by ring

/-- **Proposition I.4.2, analytic core in the shape of Case 3**: the multiplicative
error of (I.4.6) is `Ebar_1 = 1 - (1 - E_0)(1 - E_1)`; if it is an infinitesimal
along `atTop` then `f r / ((a/A) r^a) -> 1`, with only an a.e. differential equation
and absolute continuity assumed on `f`. -/
theorem first_moment_asymptotic_at_critical_ae {f E0 E1 : ℝ → ℝ} {A α r₀ : ℝ} {B : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - (1 - (1 - E0 t) * (1 - E1 t))) * t ^ (-α - 1) * (f t) ^ 2) t)
    (h0meas : Measurable E0) (h1meas : Measurable E1)
    (h0 : Tendsto E0 atTop (𝓝 0)) (h1 : Tendsto E1 atTop (𝓝 0))
    (h0b : ∀ r, |E0 r| ≤ 1 / 8) (h1nn : ∀ r, 0 ≤ E1 r) (h1B : ∀ r, E1 r ≤ B) :
    Tendsto (fun r => f r / (α / A * r ^ α)) atTop (𝓝 1) := by
  have hmeas : Measurable (fun r => 1 - (1 - E0 r) * (1 - E1 r)) :=
    measurable_const.sub ((measurable_const.sub h0meas).mul (measurable_const.sub h1meas))
  refine first_moment_asymptotic_ae hA hα hr₀ hac hpos hinf hae hmeas
    (fun r _ => abs_one_sub_mul_le h0b h1nn h1B r) (tendsto_one_sub_mul h0 h1)

/-- **Proposition I.4.2, second assertion for Case 3, analytic core**: if the
multiplicative error of (I.4.6) is built from log-integrable error functions
`E_0`, `E_1`, then the normalized first-moment error is itself log-integrable. -/
theorem first_moment_error_logIntegrable_at_critical_ae {f E0 E1 : ℝ → ℝ}
    {A α r₀ B : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - (1 - (1 - E0 t) * (1 - E1 t))) * t ^ (-α - 1) * (f t) ^ 2) t)
    (h0log : PercLib.CriticalLRP.Analysis.IsLogErrorFunction E0)
    (h1log : PercLib.CriticalLRP.Analysis.IsLogErrorFunction E1)
    (h0b : ∀ r, |E0 r| ≤ 1 / 8) (h1nn : ∀ r, 0 ≤ E1 r) (h1B : ∀ r, E1 r ≤ B)
    (hHmeas : Measurable (fun r => A / α * r ^ (-α) * f r - 1)) :
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable
      (fun r => A / α * r ^ (-α) * f r - 1) := by
  have hmlog := isLogErrorFunction_one_sub_mul h0log h1log h0b h1nn h1B
  have h0 : Tendsto E0 atTop (𝓝 0) := h0log.2
  have h1 : Tendsto E1 atTop (𝓝 0) := h1log.2
  have hmeas : Measurable (fun r => 1 - (1 - E0 r) * (1 - E1 r)) :=
    measurable_const.sub
      ((measurable_const.sub h0log.1.1).mul (measurable_const.sub h1log.1.1))
  exact first_moment_error_logIntegrable_ae hA hα hr₀ hac hpos hinf hae hmeas
    (fun r _ => abs_one_sub_mul_le h0b h1nn h1B r) (tendsto_one_sub_mul h0 h1) hmlog.1 hHmeas

/-- The normalized first-moment error `H_r = (A/a) r^(-a) f r - 1` of (I.4.6) tends to
`0`; equivalently `(A/a) r^(-a) f r` and `f r / ((a/A) r^a)` agree and the ratio tends
to `1`. -/
theorem tendsto_error_at_critical_ae {f E0 E1 : ℝ → ℝ} {A α r₀ B : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - (1 - (1 - E0 t) * (1 - E1 t))) * t ^ (-α - 1) * (f t) ^ 2) t)
    (h0meas : Measurable E0) (h1meas : Measurable E1)
    (h0 : Tendsto E0 atTop (𝓝 0)) (h1 : Tendsto E1 atTop (𝓝 0))
    (h0b : ∀ r, |E0 r| ≤ 1 / 8) (h1nn : ∀ r, 0 ≤ E1 r) (h1B : ∀ r, E1 r ≤ B) :
    Tendsto (fun r => A / α * r ^ (-α) * f r - 1) atTop (𝓝 0) := by
  have h := first_moment_asymptotic_at_critical_ae hA hα hr₀ hac hpos hinf hae
    h0meas h1meas h0 h1 h0b h1nn h1B
  have hc1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h1' : Tendsto (fun r => f r / (α / A * r ^ α) - 1) atTop (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ => f r / (α / A * r ^ α) - 1) atTop (𝓝 (1 - 1)) :=
      h.sub hc1
    simpa using h2
  refine h1'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hrm : r ^ (-α) = (r ^ α)⁻¹ := Real.rpow_neg hr.le α
  rw [hrm]
  have hAne : A ≠ 0 := ne_of_gt hA
  have hαne : α ≠ 0 := ne_of_gt hα
  field_simp

/-- **Proposition I.4.2, second assertion, Case 3 shape, analytic core**: the
normalized first-moment error is a logarithmically integrable error function, i.e. both
`∫^∞ |H_r| dr/r < ∞` and `H_r -> 0`. -/
theorem first_moment_error_isLogErrorFunction_at_critical_ae {f E0 E1 : ℝ → ℝ}
    {A α r₀ B : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - (1 - (1 - E0 t) * (1 - E1 t))) * t ^ (-α - 1) * (f t) ^ 2) t)
    (h0log : PercLib.CriticalLRP.Analysis.IsLogErrorFunction E0)
    (h1log : PercLib.CriticalLRP.Analysis.IsLogErrorFunction E1)
    (h0b : ∀ r, |E0 r| ≤ 1 / 8) (h1nn : ∀ r, 0 ≤ E1 r) (h1B : ∀ r, E1 r ≤ B)
    (hHmeas : Measurable (fun r => A / α * r ^ (-α) * f r - 1)) :
    PercLib.CriticalLRP.Analysis.IsLogErrorFunction
      (fun r => A / α * r ^ (-α) * f r - 1) :=
  ⟨first_moment_error_logIntegrable_at_critical_ae hA hα hr₀ hac hpos hinf hae
      h0log h1log h0b h1nn h1B hHmeas,
    tendsto_error_at_critical_ae hA hα hr₀ hac hpos hinf hae h0log.1.1 h1log.1.1
      h0log.2 h1log.2 h0b h1nn h1B⟩

/-! ## Lemma I.4.5(1) and (2) with an almost-everywhere derivative

The one-sided comparisons are what Lemma I.4.9's bootstrap (p. 37) and Lemma I.4.10 use,
both times on a cut-off cluster mass `r |-> E_{b,r}|K|` and therefore subject to the same
corner problem.  They reduce to the sign of the integral in the exact identity, so no
extra analysis is needed beyond `inv_eq_of_ode_ae`. -/

/-- The comparison function `g r = 1/f r - (A/a) r^(-a)`: on `[r, R]`,
`g r - g R = -A * int_r^R h s s^(-a-1) ds`. -/
theorem inv_sub_rpow_sub_eq {f h : ℝ → ℝ} {A α r₀ C r R : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (hr : r₀ ≤ r) (hrR : r ≤ R) :
    (f r)⁻¹ - A / α * r ^ (-α) - ((f R)⁻¹ - A / α * R ^ (-α))
      = -(A * ∫ s in r..R, h s * s ^ (-α - 1)) := by
  have h := inv_eq_of_ode_ae hA hα hr₀ hac hpos hae hmeas hC hr hrR
  linarith [h]

/-- `g` is nonincreasing when the multiplicative error `h` is nonpositive. -/
theorem inv_sub_rpow_antitone {f h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (hneg : ∀ t, r₀ ≤ t → h t ≤ 0)
    {r R : ℝ} (hr : r₀ ≤ r) (hrR : r ≤ R) :
    (f R)⁻¹ - A / α * R ^ (-α) ≤ (f r)⁻¹ - A / α * r ^ (-α) := by
  have hkey := inv_sub_rpow_sub_eq hA hα hr₀ hac hpos hae hmeas hC hr hrR
  have hnn : 0 ≤ ∫ s in r..R, -(h s * s ^ (-α - 1)) := by
    refine intervalIntegral.integral_nonneg hrR ?_
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le (lt_of_lt_of_le hr₀ hr) hu.1
    have h1 : h u ≤ 0 := hneg u (le_trans hr hu.1)
    have h2 : 0 < u ^ (-α - 1) := Real.rpow_pos_of_pos hu0 _
    have : h u * u ^ (-α - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h1 h2.le
    simpa using this
  have hI : ∫ s in r..R, h s * s ^ (-α - 1) ≤ 0 := by
    have h1 : ∫ s in r..R, -(h s * s ^ (-α - 1)) = -(∫ s in r..R, h s * s ^ (-α - 1)) :=
      intervalIntegral.integral_neg
    rw [h1] at hnn
    linarith
  nlinarith [hkey, hI, hA]

/-- **Lemma I.4.5(1), corner-safe form**: if `f' >= A(1-h) r^(-a-1) f^2` a.e. with
`h <= 0`, then `f r <= (a/A) r^a` for every `r >= r0`. -/
theorem lemma_I_4_5_one_ae {f h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (hneg : ∀ t, r₀ ≤ t → h t ≤ 0) :
    ∀ r, r₀ ≤ r → f r ≤ (α / A) * r ^ α := by
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  have hcoef : 0 < A / α := by positivity
  have hrm : (0 : ℝ) < A / α * r ^ (-α) :=
    mul_pos hcoef (Real.rpow_pos_of_pos hr0 _)
  -- it suffices that `g r = 1/f r - (A/a) r^(-a)` is nonnegative
  have hgr : 0 ≤ (f r)⁻¹ - A / α * r ^ (-α) := by
    by_contra hlt
    have hlt' : (f r)⁻¹ - A / α * r ^ (-α) < 0 := not_le.1 hlt
    have hε : 0 < -((f r)⁻¹ - A / α * r ^ (-α)) := by linarith
    have htend : Tendsto (fun R : ℝ => A / α * R ^ (-α)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop hα).const_mul (A / α)
      simpa using h
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.1
      (htend.eventually (eventually_lt_nhds hε))
    set R : ℝ := max R₀ r with hRdef
    have hRr : r ≤ R := le_max_right _ _
    have hRge : R₀ ≤ R := le_max_left _ _
    have hRsmall : A / α * R ^ (-α) < -((f r)⁻¹ - A / α * r ^ (-α)) := hR₀ R hRge
    have hanti := inv_sub_rpow_antitone hA hα hr₀ hac hpos hae hmeas hC hneg
      hr hRr
    have hposR : 0 < (f R)⁻¹ := inv_pos.2 (hpos R (le_trans hr hRr))
    linarith
  -- `(f r)^(-1) >= (A/a) r^(-a)` gives `f r <= (a/A) r^a`
  have h1 : A / α * r ^ (-α) ≤ (f r)⁻¹ := by linarith
  have h2 : f r ≤ (A / α * r ^ (-α))⁻¹ := by
    have hfinv : 0 < (f r)⁻¹ := inv_pos.2 (hpos r hr)
    have h2' := (inv_le_inv₀ hfinv hrm).2 h1
    simpa using h2'
  have h3 : (A / α * r ^ (-α))⁻¹ = (α / A) * r ^ α := by
    have hAne : A ≠ 0 := ne_of_gt hA
    have hαne : α ≠ 0 := ne_of_gt hα
    rw [Real.rpow_neg hr0.le α]
    field_simp
  rwa [h3] at h2

/-- **Lemma I.4.5(2), corner-safe form**: if `f' <= A(1-h) r^(-a-1) f^2` a.e. with
`h >= 0` and `f -> ∞`, then `f r >= (a/A) r^a` for every `r >= r0`. -/
theorem lemma_I_4_5_two_ae {f h : ℝ → ℝ} {A α r₀ C : ℝ}
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2) t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (hposh : ∀ t, r₀ ≤ t → 0 ≤ h t) :
    ∀ r, r₀ ≤ r → (α / A) * r ^ α ≤ f r := by
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hrm : (0 : ℝ) < A / α * r ^ (-α) :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos hr0 _)
  -- `g` is nondecreasing and `g -> 0`, hence `g r <= 0`
  have hmono : ∀ R, r ≤ R →
      (f r)⁻¹ - A / α * r ^ (-α) ≤ (f R)⁻¹ - A / α * R ^ (-α) := by
    intro R hrR
    have hkey := inv_sub_rpow_sub_eq hA hα hr₀ hac hpos hae hmeas hC hr hrR
    have hnn : 0 ≤ ∫ s in r..R, h s * s ^ (-α - 1) := by
      refine intervalIntegral.integral_nonneg hrR ?_
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le (lt_of_lt_of_le hr₀ hr) hu.1
      exact mul_nonneg (hposh u (le_trans hr hu.1)) (Real.rpow_nonneg hu0.le _)
    nlinarith [hkey, hnn, hA]
  have hlim : Tendsto (fun R : ℝ => (f R)⁻¹ - A / α * R ^ (-α)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => (f R)⁻¹) atTop (𝓝 0) := hinf.inv_tendsto_atTop
    have h2 : Tendsto (fun R : ℝ => A / α * R ^ (-α)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop hα).const_mul (A / α)
      simpa using h
    have h3 := h1.sub h2
    simpa using h3
  have hle : (f r)⁻¹ - A / α * r ^ (-α) ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨r, hmono⟩)
  have h1 : (f r)⁻¹ ≤ A / α * r ^ (-α) := by linarith
  have hfr : 0 < f r := hpos r hr
  have h2' := (inv_le_inv₀ hrm (inv_pos.2 hfr)).2 h1
  have this : (A / α * r ^ (-α))⁻¹ ≤ f r := by simpa using h2'
  have h3 : (A / α * r ^ (-α))⁻¹ = (α / A) * r ^ α := by
    have hAne : A ≠ 0 := ne_of_gt hA
    have hαne : α ≠ 0 := ne_of_gt hα
    rw [Real.rpow_neg hr0.le α]
    field_simp
  rwa [h3] at this

/-! ## The corner set of the cut-off profile is null

`PercLib.CriticalLRP.FiniteVolume.hasDerivWithinAt_cutoffProfile_Iic` and
`..._Ioi` identify the two one-sided derivatives of `r' |-> cutoffProfile K r' s` at
`r' = s`, and `not_hasDerivAt_cutoffProfile` shows the two-sided derivative fails
there. The exceptional radii are therefore the edge lengths `s = dist 0 y` of the
model. The next two declarations record that this set is countable, hence null, so
that any `r`-derivative which exists off it exists almost everywhere — which is
exactly the hypothesis of the corner-safe Lemma I.4.5 above. -/

/-- The set of radii at which some edge of the model has its length is countable (it is
the range of `y |-> dist 0 y` on the countable lattice). -/
theorem countable_cornerSet (M : PercLib.CriticalLRP.Orchestration.SourceModelData) :
    {r : ℝ | ∃ y : M.V, M.S.dist 0 y = r}.Countable :=
  Set.countable_range (fun y : M.V => M.S.dist 0 y)

/-- **The corner-safe hypothesis is the one the model supplies.** If a function of the
cut-off radius has the `r`-derivative `F' r` at every radius that is not an edge length,
then it has that derivative almost everywhere. -/
theorem ae_hasDerivAt_of_off_corner
    (M : PercLib.CriticalLRP.Orchestration.SourceModelData) {F F' : ℝ → ℝ}
    (h : ∀ r, (∀ y : M.V, M.S.dist 0 y ≠ r) → HasDerivAt F (F' r) r) :
    ∀ᵐ r ∂(volume : Measure ℝ), HasDerivAt F (F' r) r := by
  refine ae_hasDerivAt_of_countable_not (countable_cornerSet M) ?_
  intro r hr
  exact h r (fun y hy => hr ⟨y, hy⟩)

end PercLib.CriticalLRP.CornerSafe
