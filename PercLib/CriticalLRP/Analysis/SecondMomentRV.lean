/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwyrvajs`, member `m1`,
direction (A), at production base `f6643492ceecda8b5282ee0d6f3eebafb44ee6f5`.

# Second-moment regular variation from the linearly-scaled ODE, corner-safe

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.  Proposition I.4.15 (second-moment asymptotics), together with the
displayed identities (I.4.14)-(I.4.16) of its proof: the `p = 2` radial identity is
rewritten there as the *linear* ODE

  `d/dr E_{b_c,r}|K|^2 = 3α (1 - Ebar_{2,r}) r⁻¹ E_{b_c,r}|K|^2`     (I.4.15)

with a scalar error function `Ebar_{2,r}` satisfying `Ebar_{2,r} → 0` (Cases 1 and 2) and
being logarithmically integrable when `d > 3α`; Lemma I.2.12 is then invoked with `a = 3α`.

## Why this file

`Analysis/RegularVariation.lean` proves Lemma I.2.12 (`lemma_I_2_12_rv`,
`lemma_I_2_12_tendsto`) but assumes a *pointwise* derivative `HasDerivAt f (f' t) t` at
**every** radius of the tail.  The second (and first) cutoff moment does not have that:
the cutoff profile has a corner at every attained edge length, a countable hence null set,
so what the model supplies is

* absolute continuity of `r ↦ E_{b_c,r}|K|^2` on every compact window of the tail, and
* the ODE only at almost every radius.

The declarations below prove the same two conclusions of Lemma I.2.12 — regular variation
of index `a`, and its normalised refinement under logarithmic integrability of the error —
from exactly that weaker, corner-safe hypothesis set, using the *existing* accepted
machinery rather than re-deriving it:

* `Analysis.normalized_increment_of_driving_ode_ac` (the a.e. integrating-factor increment)
  with zero driving term gives the exact multiplicative solution;
* `Analysis.regularlyVarying_powerExpWeight` gives regular variation of its exponential
  weight.

`ode_solution_mul_ae` is the corner-safe form of `Analysis.ode_solution_mul`.

## Scope

Everything here is conditional on the error function `E`; **no model error function is
supplied or asserted to exist**.  The instantiation at the actual cutoff moment is a
separate statement with the model side kept as explicit hypotheses.  In particular this
file does not prove Proposition I.4.15.
-/
module

public import PercLib.CriticalLRP.Analysis.AENormalizedIncrement
public import PercLib.CriticalLRP.Analysis.RVAlgebra

/-! # Corner-safe regular variation for the second-moment linear ODE -/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.SecondMomentRV

open PercLib.CriticalLRP.Analysis

/-! ## Two elementary facts about the exponential weight -/

/-- On a window `[r₀,R]`, the cut error `errorTail r₀ h` integrates like `h`: the two
functions differ only at the single point `r₀`. -/
theorem intervalIntegral_errorTail_div_eq {h : ℝ → ℝ} {r₀ R : ℝ} (hr : r₀ ≤ R) :
    ∫ s in r₀..R, errorTail r₀ h s / s = ∫ s in r₀..R, h s / s := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with s hs
  rw [uIoc_of_le hr] at hs
  have hs' : s ∈ Ioi r₀ := hs.1
  rw [errorTail, indicator_of_mem hs']

/-- `powerExpWeight` at its own base is the pure power: the error integral over `[r₀,r₀]`
vanishes. -/
theorem powerExpWeight_self {h : ℝ → ℝ} {r₀ a : ℝ} :
    powerExpWeight r₀ a h r₀ = r₀ ^ a := by
  rw [powerExpWeight, intervalIntegral.integral_same]
  simp

/-- `powerExpWeight` written in the paper's `(R/r)^a` shape. -/
theorem powerExpWeight_eq_mul {h : ℝ → ℝ} {r₀ a R : ℝ} (hr₀ : 0 < r₀) (hr₀R : r₀ ≤ R) :
    powerExpWeight r₀ a h R =
      r₀ ^ a * ((R / r₀) ^ a * Real.exp (-(a * ∫ s in r₀..R, h s / s))) := by
  have hRpos : 0 < R := lt_of_lt_of_le hr₀ hr₀R
  have hne : r₀ ^ a ≠ 0 := (Real.rpow_pos_of_pos hr₀ a).ne'
  rw [powerExpWeight, intervalIntegral_errorTail_div_eq hr₀R, Real.div_rpow hRpos.le hr₀.le,
    div_eq_mul_inv]
  rw [show r₀ ^ a * (R ^ a * (r₀ ^ a)⁻¹ * Real.exp (-(a * ∫ s in r₀..R, h s / s)))
      = (r₀ ^ a * (r₀ ^ a)⁻¹) * (R ^ a * Real.exp (-(a * ∫ s in r₀..R, h s / s))) by ring,
    mul_inv_cancel₀ hne, one_mul]

/-- A non-zero constant multiple of a regularly varying function is regularly varying of
the same index.  (`Analysis.RVAlgebra` has products, inverses and powers, but not this.) -/
theorem regularlyVaryingAtTop_const_mul {f : ℝ → ℝ} {a c : ℝ} (hc : c ≠ 0)
    (hf : RegularlyVaryingAtTop f a) :
    RegularlyVaryingAtTop (fun x : ℝ => c * f x) a := by
  refine ⟨?_, fun l hl => ?_⟩
  · filter_upwards [hf.1] with x hx
    exact mul_ne_zero hc hx
  · have hcomp : Tendsto (fun x : ℝ => f (l * x) / f x) atTop (𝓝 (l ^ a)) := hf.2 l hl
    refine hcomp.congr' ?_
    filter_upwards with x
    rw [mul_div_mul_left _ _ hc]

/-! ## The exact multiplicative solution with an a.e. derivative -/

/-- **Corner-safe form of `Analysis.ode_solution_mul`.**  If `f` is absolutely continuous
on every window `[r₀,R]` of the tail and satisfies `f' = a (1 - h) f / r` at almost every
radius, with `h` measurable and `|h| ≤ 1` on the tail, then for `r₀ ≤ r ≤ R`

  `f R = f r * (R/r)^a * exp (-(a ∫_r^R h s ds/s))`.

No differentiability of `f` is claimed at the exceptional radii and no positivity of `f`
is used.  The proof divides by the exact integrating factor `powerExpWeight r a h` — for
which the increment identity of `Analysis.normalized_increment_of_driving_ode_ac` with zero
driving term is available off a null set — and then reads off the ratio. -/
theorem ode_solution_mul_ae {f f' h : ℝ → ℝ} {a r₀ : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)), HasDerivAt f (f' t) t)
    (hode : ∀ᵐ t ∂(volume.restrict (Ici r₀)), f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (h1 : ∀ t, r₀ ≤ t → |h t| ≤ 1)
    {r R : ℝ} (hr : r₀ ≤ r) (hrR : r ≤ R) :
    f R = f r * (R / r) ^ a * Real.exp (-(a * ∫ s in r..R, h s / s)) := by
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR
  -- absolute continuity on the window `[r,R]`
  have hacR : AbsolutelyContinuousOnInterval f r R :=
    (hac R (le_trans hr hrR)).mono (by
      rw [uIcc_of_le (le_trans hr hrR), uIcc_of_le hrR]
      exact Icc_subset_Icc hr le_rfl)
  -- the a.e. hypotheses, transported to the window
  have hae' : ∀ᵐ x : ℝ, x ∈ Ioc r R → HasDerivAt f (f' x) x := by
    have h := (ae_restrict_iff' measurableSet_Ici).1 hae
    filter_upwards [h] with x hx hxmem
    exact hx (le_trans hr hxmem.1.le)
  have hode' : ∀ᵐ x : ℝ, x ∈ Ioc r R →
      f' x = (1 - h x) * a * f x / x + (fun _ : ℝ => 0) x / x := by
    have h := (ae_restrict_iff' measurableSet_Ici).1 hode
    filter_upwards [h] with x hx hxmem
    rw [hx (le_trans hr hxmem.1.le)]
    ring
  have h1' : ∀ x : ℝ, r ≤ x → |h x| ≤ 1 := fun x hx => h1 x (le_trans hr hx)
  -- the a.e. integrating-factor increment with zero driving term
  have key := normalized_increment_of_driving_ode_ac (f := f) (f' := f') (h := fun _ : ℝ => 0)
    (δ := h) (a := a) (r₀ := r) (R := R) ha hr0 hrR hacR hae' hmeas h1' hode'
  have hzero : ∫ s in r..R, (fun _ : ℝ => 0) s / (s * powerExpWeight r a h s) = 0 := by
    simp
  rw [hzero] at key
  have hratio : f R * (powerExpWeight r a h R)⁻¹ = f r * (r ^ a)⁻¹ := by
    rw [sub_eq_zero] at key
    rwa [powerExpWeight_self] at key
  have hWRne : powerExpWeight r a h R ≠ 0 := by
    rw [powerExpWeight]
    exact mul_ne_zero (Real.rpow_pos_of_pos hR0 a).ne' (Real.exp_pos _).ne'
  have hdiv : f R / powerExpWeight r a h R = f r / r ^ a := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact hratio
  have hstep : f R = f r / r ^ a * powerExpWeight r a h R := by
    have h := congrArg (fun z => z * powerExpWeight r a h R) hdiv
    rw [div_mul_cancel₀ (f R) hWRne] at h
    exact h
  have hrne : r ^ a ≠ 0 := (Real.rpow_pos_of_pos hr0 a).ne'
  rw [hstep, powerExpWeight_eq_mul (h := h) (a := a) (r₀ := r) (R := R) hr0 hrR,
    Real.div_rpow hR0.le hr0.le, div_eq_mul_inv]
  field_simp

/-- **The logarithmic form of (I.4.15).**  Under the hypotheses of `ode_solution_mul_ae` and
positivity of `f` on the tail, for `r₀ ≤ r ≤ R`

  `log (f R) - log (f r) = a log (R/r) - a ∫_r^R h s ds/s`,

the display used in the proof of Lemma I.2.12 (equivalently: `log ∘ f` has a.e. derivative
`a (1 - h)/r`).  This is the form in which the scaling ratio `f (λ r) / f r` is evaluated. -/
theorem log_ratio_of_ae_linear_ode {f f' h : ℝ → ℝ} {a r₀ : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)), HasDerivAt f (f' t) t)
    (hode : ∀ᵐ t ∂(volume.restrict (Ici r₀)), f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (h1 : ∀ t, r₀ ≤ t → |h t| ≤ 1)
    {r R : ℝ} (hr : r₀ ≤ r) (hrR : r ≤ R) :
    Real.log (f R) - Real.log (f r) = a * Real.log (R / r) - a * ∫ s in r..R, h s / s := by
  have hsol := ode_solution_mul_ae ha hr₀ hac hae hode hmeas h1 hr hrR
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR
  have hfr : 0 < f r := hpos r hr
  have hq : 0 < R / r := div_pos hR0 hr0
  have hpow : 0 < (R / r) ^ a := Real.rpow_pos_of_pos hq a
  have hexp : 0 < Real.exp (-(a * ∫ s in r..R, h s / s)) := Real.exp_pos _
  rw [hsol, Real.log_mul (mul_ne_zero (ne_of_gt hfr) (ne_of_gt hpow)) (ne_of_gt hexp),
    Real.log_mul (ne_of_gt hfr) (ne_of_gt hpow), Real.log_rpow hq, Real.log_exp]
  ring

/-! ## Lemma I.2.12 with an a.e. derivative -/

/-- **Lemma I.2.12, first part, corner-safe form.**  If `f > 0` on `[r₀,∞)` is absolutely
continuous on every compact window of the tail, satisfies `f' = a (1 - h) f / r` at almost
every radius, and `h` is measurable with `h → 0`, then `f` is regularly varying of index
`a`.

This is `Analysis.lemma_I_2_12_rv` with the pointwise derivative on the whole tail
replaced by interval absolute continuity plus an a.e. derivative. -/
theorem regularlyVarying_of_ae_linear_ode {f f' h : ℝ → ℝ} {a r₀ : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)), HasDerivAt f (f' t) t)
    (hode : ∀ᵐ t ∂(volume.restrict (Ici r₀)), f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (h0 : Tendsto h atTop (𝓝 0)) :
    RegularlyVaryingAtTop f a := by
  -- shrink the tail so that `|h| ≤ 1` there
  obtain ⟨r₁, hr₁, h1⟩ : ∃ r₁ : ℝ, r₀ ≤ r₁ ∧ ∀ t : ℝ, r₁ ≤ t → |h t| ≤ 1 := by
    obtain ⟨X, hX⟩ := Metric.tendsto_atTop.1 h0 1 one_pos
    refine ⟨max r₀ X, le_max_left _ _, fun t ht => ?_⟩
    have h := hX t (le_trans (le_max_right r₀ X) ht)
    rw [Real.dist_eq, sub_zero, abs_lt] at h
    exact abs_le.2 ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le hr₀ hr₁
  have hac₁ : ∀ R : ℝ, r₁ ≤ R → AbsolutelyContinuousOnInterval f r₁ R := by
    intro R hR
    exact (hac R (le_trans hr₁ hR)).mono (by
      rw [uIcc_of_le (le_trans hr₁ hR), uIcc_of_le hR]
      exact Icc_subset_Icc hr₁ le_rfl)
  have hae₁ : ∀ᵐ t ∂(volume.restrict (Ici r₁)), HasDerivAt f (f' t) t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ici).1 hae] with t ht ht₁
    exact ht (le_trans hr₁ ht₁)
  have hode₁ : ∀ᵐ t ∂(volume.restrict (Ici r₁)), f' t = a * (1 - h t) * f t / t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ici).1 hode] with t ht ht₁
    exact ht (le_trans hr₁ ht₁)
  -- `f` is eventually a constant multiple of the exact power/error weight
  have hfeq : f =ᶠ[atTop] fun R : ℝ => (f r₁ / r₁ ^ a) * powerExpWeight r₁ a h R := by
    filter_upwards [eventually_ge_atTop r₁] with R hR
    have hsol := ode_solution_mul_ae ha hr₁pos hac₁ hae₁ hode₁ hmeas h1 le_rfl hR
    have hW := powerExpWeight_eq_mul (h := h) (a := a) (r₀ := r₁) (R := R) hr₁pos hR
    rw [hsol, hW]
    field_simp
  have hW : RegularlyVaryingAtTop (powerExpWeight r₁ a h) a :=
    regularlyVarying_powerExpWeight ha hr₁pos hmeas h0 h1
  have hc : f r₁ / r₁ ^ a ≠ 0 :=
    div_ne_zero (ne_of_gt (hpos r₁ hr₁)) (Real.rpow_pos_of_pos hr₁pos a).ne'
  have hcW : RegularlyVaryingAtTop (fun R : ℝ => (f r₁ / r₁ ^ a) * powerExpWeight r₁ a h R) a :=
    regularlyVaryingAtTop_const_mul hc hW
  refine ⟨?_, fun l hl => ?_⟩
  · filter_upwards [hfeq, hcW.1] with R hR hne
    rwa [hR]
  · have hratio := hcW.2 l hl
    refine hratio.congr' ?_
    have hl1 : Tendsto (fun x : ℝ => l * x) atTop atTop :=
      Tendsto.const_mul_atTop hl tendsto_id
    filter_upwards [hfeq, hl1.eventually hfeq] with x hx hxl
    rw [hxl, hx]

/-- **Lemma I.2.12, second part, corner-safe form.**  With the hypotheses of
`regularlyVarying_of_ae_linear_ode` and `h` additionally logarithmically integrable, there
is `A > 0` with `f r / r^a → A`.

This is `Analysis.lemma_I_2_12_tendsto` with the pointwise derivative on the whole tail
replaced by interval absolute continuity plus an a.e. derivative. -/
theorem tendsto_div_of_ae_linear_ode {f f' h : ℝ → ℝ} {a r₀ : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)), HasDerivAt f (f' t) t)
    (hode : ∀ᵐ t ∂(volume.restrict (Ici r₀)), f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (h0 : Tendsto h atTop (𝓝 0))
    (hlog : LogarithmicallyIntegrable h) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun r : ℝ => f r / r ^ a) atTop (𝓝 A) := by
  obtain ⟨r₂, hr₂, hint⟩ := hlog.2
  obtain ⟨r₃, hr₃, h3⟩ : ∃ r₃ : ℝ, r₀ ≤ r₃ ∧ ∀ t : ℝ, r₃ ≤ t → |h t| ≤ 1 := by
    obtain ⟨X, hX⟩ := Metric.tendsto_atTop.1 h0 1 one_pos
    refine ⟨max r₀ X, le_max_left _ _, fun t ht => ?_⟩
    have h := hX t (le_trans (le_max_right r₀ X) ht)
    rw [Real.dist_eq, sub_zero, abs_lt] at h
    exact abs_le.2 ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hr₃pos : 0 < r₃ := lt_of_lt_of_le hr₀ hr₃
  set R₀ : ℝ := max r₃ r₂ with hR₀def
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le hr₃pos (le_max_left _ _)
  have hr₀R₀ : r₀ ≤ R₀ := le_trans hr₃ (le_max_left _ _)
  have hR₀r₃ : r₃ ≤ R₀ := le_max_left _ _
  have hR₀r₂ : r₂ ≤ R₀ := le_max_right _ _
  have h1₀ : ∀ t : ℝ, R₀ ≤ t → |h t| ≤ 1 := fun t ht => h3 t (le_trans hR₀r₃ ht)
  have hac₀ : ∀ R : ℝ, R₀ ≤ R → AbsolutelyContinuousOnInterval f R₀ R := by
    intro R hR
    exact (hac R (le_trans hr₀R₀ hR)).mono (by
      rw [uIcc_of_le (le_trans hr₀R₀ hR), uIcc_of_le hR]
      exact Icc_subset_Icc hr₀R₀ le_rfl)
  have hae₀ : ∀ᵐ t ∂(volume.restrict (Ici R₀)), HasDerivAt f (f' t) t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ici).1 hae] with t ht ht₀
    exact ht (le_trans hr₀R₀ ht₀)
  have hode₀ : ∀ᵐ t ∂(volume.restrict (Ici R₀)), f' t = a * (1 - h t) * f t / t := by
    refine (ae_restrict_iff' measurableSet_Ici).2 ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ici).1 hode] with t ht ht₀
    exact ht (le_trans hr₀R₀ ht₀)
  -- the error is integrable against `ds/s` on the tail
  have hint' : IntegrableOn (fun s : ℝ => h s / s) (Ioi R₀) := by
    refine ((hint.mono_set (Ioi_subset_Ioi hR₀r₂)).mono' ?_ ?_)
    · exact (hmeas.div measurable_id).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := lt_of_lt_of_le hR₀pos (le_of_lt hs)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hs0]
  -- the exact solution, normalised by `r^a`
  have hquot : ∀ R : ℝ, R₀ ≤ R →
      f R / R ^ a = (f R₀ / R₀ ^ a) *
        Real.exp (-(a * ∫ s in R₀..R, h s / s)) := by
    intro R hR
    have hsol := ode_solution_mul_ae ha hR₀pos hac₀ hae₀ hode₀ hmeas h1₀ le_rfl hR
    have hRpos : 0 < R := lt_of_lt_of_le hR₀pos hR
    have hneR : R ^ a ≠ 0 := (Real.rpow_pos_of_pos hRpos a).ne'
    have hneR₀ : R₀ ^ a ≠ 0 := (Real.rpow_pos_of_pos hR₀pos a).ne'
    rw [hsol, Real.div_rpow hRpos.le hR₀pos.le, div_eq_mul_inv, div_eq_mul_inv]
    field_simp
  have hlim : Tendsto
      (fun R : ℝ => (f R₀ / R₀ ^ a) * Real.exp (-(a * ∫ s in R₀..R, h s / s)))
      atTop (𝓝 ((f R₀ / R₀ ^ a) *
        Real.exp (-(a * ∫ s in Ioi R₀, h s / s)))) := by
    have hInt : Tendsto (fun R : ℝ => ∫ s in R₀..R, h s / s) atTop
        (𝓝 (∫ s in Ioi R₀, h s / s)) :=
      intervalIntegral_tendsto_integral_Ioi R₀ hint' tendsto_id
    have h2 : Tendsto (fun R : ℝ => -(a * ∫ s in R₀..R, h s / s)) atTop
        (𝓝 (-(a * ∫ s in Ioi R₀, h s / s))) := (hInt.const_mul a).neg
    have h3 : Tendsto (fun R : ℝ => Real.exp (-(a * ∫ s in R₀..R, h s / s))) atTop
        (𝓝 (Real.exp (-(a * ∫ s in Ioi R₀, h s / s)))) :=
      (Real.continuous_exp.tendsto _).comp h2
    exact h3.const_mul _
  refine ⟨(f R₀ / R₀ ^ a) * Real.exp (-(a * ∫ s in Ioi R₀, h s / s)), ?_, ?_⟩
  · have hf : 0 < f R₀ := hpos R₀ hr₀R₀
    have hrp : 0 < R₀ ^ a := Real.rpow_pos_of_pos hR₀pos a
    positivity
  · refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop R₀] with R hR
    exact (hquot R hR).symm

/-! ## The second-moment instance: coefficient `3α` and the paper's error display -/

/-- **Second-moment regular variation from the actual linear error form (I.4.15).**

If `f > 0` on `[r₀,∞)` is absolutely continuous on every compact window of the tail and
satisfies, at almost every radius,

  `f' = 3α (1 - E) r⁻¹ f`,

with `E` measurable and `E → 0`, then `f` is regularly varying of index `3α`.

In the application `f = r ↦ E_{b_c,r}|K|^2` and `E = Ebar_{2,r}` of (I.4.15); the
hypothesis is *exactly* the linear display with the second-moment coefficient `3α` and no
independent driving term.  Note the quantifier order: `E` is a single function fixed
before the limit `r → ∞`, and the `r > 0` domain is carried by `0 < r₀`. -/
theorem secondMoment_regularlyVarying {f E : ℝ → ℝ} {α r₀ : ℝ}
    (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (3 * α * (1 - E t) * f t / t) t)
    (hmeas : Measurable E) (h0 : Tendsto E atTop (𝓝 0)) :
    RegularlyVaryingAtTop f (3 * α) := by
  have h3 : 0 < 3 * α := by linarith
  refine regularlyVarying_of_ae_linear_ode (h := E)
    (f' := fun t : ℝ => 3 * α * (1 - E t) * f t / t) h3 hr₀ hac hpos hae ?_ hmeas h0
  filter_upwards [] with t
  rfl

/-- **Second-moment regular variation from a derivative value and the ratio asymptotic.**

The model supplies the derivative in the *right-hand-side* vocabulary — the paper's (I.4.14) is
`d/dr E_{b_c,r}|K|^2 = (displayed RHS)` — and the error `Ebar_{2,r}` is defined from it by
`1 - Ebar_{2,r} = t · RHS t / (3α E_{b_c,t}|K|^2)`.  Accordingly this theorem takes the
derivative value `rhs` directly and the single asymptotic statement

  `t · rhs t / (3α f t) → 1`     (i.e. `f' ~ 3α f / t`, the hypothesis of Lemma I.2.12),

with `f` and `rhs` measurable, and concludes `RegularlyVaryingAtTop f (3α)`.  The error
function `E := 1 - t · rhs t / (3α f t)` and its measurability are *derived*, not assumed. -/
theorem secondMoment_regularlyVarying_of_rhs {f rhs : ℝ → ℝ} {α r₀ : ℝ}
    (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hfmeas : Measurable f) (hrhs : Measurable rhs)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)), HasDerivAt f (rhs t) t)
    (hratio : Tendsto (fun t : ℝ => t * rhs t / (3 * α * f t)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f (3 * α) := by
  set E : ℝ → ℝ := fun t => 1 - t * rhs t / (3 * α * f t) with hE
  have hmE : Measurable E := by
    rw [hE]
    exact measurable_const.sub
      ((measurable_id.mul hrhs).div (measurable_const.mul hfmeas))
  have hE0 : Tendsto E atTop (𝓝 0) := by
    rw [hE]
    have h : Tendsto (fun t : ℝ => 1 - t * rhs t / (3 * α * f t)) atTop (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub hratio
    simpa using h
  refine secondMoment_regularlyVarying hα hr₀ hac hpos ?_ hmE hE0
  filter_upwards [hae, ae_restrict_mem measurableSet_Ici] with t ht hmem
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₀ hmem)
  have hft : f t ≠ 0 := ne_of_gt (hpos t hmem)
  have hαne : α ≠ 0 := ne_of_gt hα
  have hval : 3 * α * (1 - E t) * f t / t = rhs t := by
    rw [hE]
    simp only
    field_simp
    ring
  rwa [hval]

/-- **Second-moment `~ A r^{3α}` from logarithmic integrability of the error.**

With the hypotheses of `secondMoment_regularlyVarying` and `E` logarithmically integrable,
`f r / r^{3α}` converges to a positive limit: the case `d > 3α` of Proposition I.4.15. -/
theorem secondMoment_tendsto_div {f E : ℝ → ℝ} {α r₀ : ℝ}
    (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (3 * α * (1 - E t) * f t / t) t)
    (hmeas : Measurable E) (h0 : Tendsto E atTop (𝓝 0))
    (hlog : LogarithmicallyIntegrable E) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun r : ℝ => f r / r ^ (3 * α)) atTop (𝓝 A) := by
  have h3 : 0 < 3 * α := by linarith
  exact tendsto_div_of_ae_linear_ode (h := E)
    (f' := fun t : ℝ => 3 * α * (1 - E t) * f t / t) h3 hr₀ hac hpos hae
    (by filter_upwards [] with t; rfl) hmeas h0 hlog

/-- The normalised form of `secondMoment_tendsto_div`: `f r / (c r^{3α}) → 1` for a
positive constant `c`. -/
theorem secondMoment_tendsto_div_normalized {f E : ℝ → ℝ} {α r₀ : ℝ}
    (hα : 0 < α) (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval f r₀ R)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt f (3 * α * (1 - E t) * f t / t) t)
    (hmeas : Measurable E) (h0 : Tendsto E atTop (𝓝 0))
    (hlog : LogarithmicallyIntegrable E) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun r : ℝ => f r / (c * r ^ (3 * α))) atTop (𝓝 1) := by
  obtain ⟨A, hA, hlim⟩ :=
    secondMoment_tendsto_div hα hr₀ hac hpos hae hmeas h0 hlog
  refine ⟨A, hA, ?_⟩
  have hcomp : Tendsto (fun r : ℝ => (f r / r ^ (3 * α)) / A) atTop (𝓝 (A / A)) :=
    hlim.div_const A
  rw [div_self (ne_of_gt hA)] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r _hr
  show (f r / r ^ (3 * α)) / A = f r / (A * r ^ (3 * α))
  rw [div_div, mul_comm]

/-! ## Non-vacuity and non-triviality of the hypotheses

Two explicit solutions of the linear error form.  The first is the pure power `r ^ (3α)`, which
checks that the hypothesis packet of `secondMoment_regularlyVarying` (absolute continuity on
compact windows, positivity, the a.e. `HasDerivAt`, measurability and `E → 0`) is jointly
satisfiable.  The second is `r ^ a (log r) ^ (-a)`, whose error function `E t = 1 / log t`
still tends to `0` but only slowly: it exhibits a regularly varying function of index `a` with a
genuine logarithmic correction, i.e. the `E → 0` half of the theorem is not a disguised power
asymptotic. -/

/-- The hypotheses of `secondMoment_regularlyVarying` are satisfiable: the pure power
`r ↦ r ^ (3α)` with zero error satisfies them, and the theorem reproduces
`RegularlyVaryingAtTop (fun r => r ^ (3α)) (3α)`. -/
theorem regularlyVarying_rpow_three (α : ℝ) (hα : 0 < α) :
    RegularlyVaryingAtTop (fun r : ℝ => r ^ (3 * α)) (3 * α) := by
  refine secondMoment_regularlyVarying (E := fun _ : ℝ => 0) hα one_pos ?_ ?_ ?_
    measurable_const tendsto_const_nhds
  · intro R hR
    exact absolutelyContinuousOnInterval_rpow (α := 3 * α) one_pos hR
  · intro t ht
    exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos ht) _
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    have hd : HasDerivAt (fun r : ℝ => r ^ (3 * α)) ((3 * α) * t ^ (3 * α - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    have hval : (3 * α) * t ^ (3 * α - 1) = 3 * α * (1 - 0) * t ^ (3 * α) / t := by
      rw [Real.rpow_sub ht0 (3 * α) 1, Real.rpow_one]
      ring
    rw [← hval]
    exact hd

/-- **A genuine logarithmic correction.**  `r ↦ r ^ a (log r) ^ (-a)` is regularly varying of
index `a`, and it solves `f' = a (1 - E) f / r` with `E t = 1 / log t → 0` on `[2,∞)`.

This is the shape of the correction that the paper expects at the critical dimension: the
function is regularly varying of index `a` but is *not* asymptotic to a constant times
`r ^ a`.  It shows that the `E → 0` hypothesis of `secondMoment_regularlyVarying` is strictly
weaker than the logarithmic integrability used for the `~ A r ^ a` refinement. -/
theorem regularlyVarying_rpow_mul_log_rpow_neg (a : ℝ) (ha : 0 < a) :
    RegularlyVaryingAtTop (fun r : ℝ => r ^ a * (Real.log r) ^ (-a)) a := by
  refine regularlyVarying_of_ae_linear_ode
    (f := fun r : ℝ => r ^ a * (Real.log r) ^ (-a))
    (f' := fun t : ℝ => a * (1 - 1 / Real.log t)
      * (t ^ a * (Real.log t) ^ (-a)) / t)
    (h := fun t : ℝ => 1 / Real.log t) ha two_pos ?_ ?_ ?_ ?_ ?_ ?_
  · -- absolute continuity on `[2,R]`: the function is `C¹` on the positive window
    intro R hR
    refine ContDiffOn.absolutelyContinuousOnInterval ?_
    rw [uIcc_of_le hR]
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx.1
    have hx0 : 0 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos (by linarith)
    have h1 : ContDiffAt ℝ 1 (fun r : ℝ => r ^ a) x :=
      Real.contDiffAt_rpow_const_of_ne (x := x) (p := a) (n := 1) hx0.ne'
    have h2 : ContDiffAt ℝ 1 Real.log x := Real.contDiffAt_log.2 hx0.ne'
    have h3 : ContDiffAt ℝ 1 (fun u : ℝ => u ^ (-a)) (Real.log x) :=
      Real.contDiffAt_rpow_const_of_ne (x := Real.log x) (p := -a) (n := 1) hlx.ne'
    exact (h1.mul (h3.comp x h2)).contDiffWithinAt
  · -- positivity
    intro t ht
    have ht0 : 0 < t := by linarith [show (2 : ℝ) ≤ t from ht]
    have hlt : 0 < Real.log t := Real.log_pos (by linarith [show (2 : ℝ) ≤ t from ht])
    exact mul_pos (Real.rpow_pos_of_pos ht0 a) (Real.rpow_pos_of_pos hlt (-a))
  · -- the a.e. derivative
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    have ht0 : 0 < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have hd1 : HasDerivAt (fun r : ℝ => r ^ a) (a * t ^ (a - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    have hdlog : HasDerivAt Real.log (1 / t) t := by
      simpa [one_div] using Real.hasDerivAt_log ht0.ne'
    have hd2 : HasDerivAt (fun r : ℝ => (Real.log r) ^ (-a))
        ((1 / t) * (-a) * (Real.log t) ^ (-a - 1)) t :=
      hdlog.rpow_const (p := -a) (Or.inl hlt.ne')
    have hd := hd1.mul hd2
    have hval : a * t ^ (a - 1) * (Real.log t) ^ (-a)
        + t ^ a * ((1 / t) * (-a) * (Real.log t) ^ (-a - 1))
        = a * (1 - 1 / Real.log t) * (t ^ a * (Real.log t) ^ (-a)) / t := by
      rw [Real.rpow_sub ht0 a 1, Real.rpow_one, Real.rpow_sub hlt (-a) 1, Real.rpow_one]
      field_simp
      ring
    rw [← hval]
    exact hd
  · -- the ODE is the definition of `f'` in this parametrisation
    filter_upwards with t
    rfl
  · exact measurable_const.div Real.measurable_log
  · refine (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards with t
    simp [one_div]

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.SecondMomentRV.intervalIntegral_errorTail_div_eq
#print axioms PercLib.CriticalLRP.SecondMomentRV.powerExpWeight_self
#print axioms PercLib.CriticalLRP.SecondMomentRV.powerExpWeight_eq_mul
#print axioms PercLib.CriticalLRP.SecondMomentRV.regularlyVaryingAtTop_const_mul
#print axioms PercLib.CriticalLRP.SecondMomentRV.ode_solution_mul_ae
#print axioms PercLib.CriticalLRP.SecondMomentRV.log_ratio_of_ae_linear_ode
#print axioms PercLib.CriticalLRP.SecondMomentRV.regularlyVarying_of_ae_linear_ode
#print axioms PercLib.CriticalLRP.SecondMomentRV.tendsto_div_of_ae_linear_ode
#print axioms PercLib.CriticalLRP.SecondMomentRV.secondMoment_regularlyVarying
#print axioms PercLib.CriticalLRP.SecondMomentRV.secondMoment_regularlyVarying_of_rhs
#print axioms PercLib.CriticalLRP.SecondMomentRV.secondMoment_tendsto_div
#print axioms PercLib.CriticalLRP.SecondMomentRV.secondMoment_tendsto_div_normalized
#print axioms PercLib.CriticalLRP.SecondMomentRV.regularlyVarying_rpow_three
#print axioms PercLib.CriticalLRP.SecondMomentRV.regularlyVarying_rpow_mul_log_rpow_neg

end PercLib.CriticalLRP.SecondMomentRV
