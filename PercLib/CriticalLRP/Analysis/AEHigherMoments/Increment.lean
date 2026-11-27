/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`, direction (2).

The integration step of Lemma I.4.22 with the pointwise derivative hypothesis replaced by
absolute continuity plus an almost-everywhere derivative.
-/
module

public import PercLib.CriticalLRP.Analysis.AEHigherMoments.Defs


/-! # Almost-everywhere higher-moment interface: Increment -/

set_option autoImplicit false

open MeasureTheory Filter Set

@[expose] public section

namespace PercLib.CriticalLRP.Analysis.AE

variable {f f' g : ℝ → ℝ} {a b : ℝ}

/-- A.e. statements on `Icc a b` are a.e. statements on the interval of integration `uIoc a b`. -/
theorem ae_uIoc_of_ae_restrict_Icc (hab : a ≤ b) {p : ℝ → Prop}
    (h : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), p x) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc a b → p x := by
  have h' := (ae_restrict_iff' measurableSet_Icc).1 h
  filter_upwards [h'] with x hx hxu
  exact hx (by rw [← uIcc_of_le hab]; exact Set.uIoc_subset_uIcc hxu)

/-- **Fundamental theorem of calculus with an a.e. derivative.**

If `f` is absolutely continuous on `uIcc a b` and `f'` is a derivative of `f` at almost every
point of `uIcc a b`, then the interval integral of `f'` is the increment of `f`.  No derivative is
claimed on the exceptional null set, and the integral does not see it. -/
theorem intervalIntegral_ae_deriv_eq_sub (hab : a ≤ b)
    (hac : AbsolutelyContinuousOnInterval f a b)
    (hae : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), HasDerivAt f (f' x) x) :
    ∫ x in a..b, f' x = f b - f a := by  -- keep
  rw [← hac.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_uIoc_of_ae_restrict_Icc hab hae] with x hx hxu
  exact (hx hxu).deriv.symm

/-- **One-sided incremental comparison with an a.e. derivative.**

If `f` is absolutely continuous on `uIcc a b`, `f'` is a derivative of `f` almost everywhere
there, and `f' ≤ g` almost everywhere there with `g` interval integrable, then
`f b - f a ≤ ∫ t in a..b, g t`.  This is the a.e. replacement of
`intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le` used in
`Analysis.Lemma_I_4_22.normalized_increment_le_of_driving_bound`; no derivative is needed at the
exceptional radii. -/
theorem sub_le_integral_of_ae_hasDerivAt_of_le (hab : a ≤ b)
    (hac : AbsolutelyContinuousOnInterval f a b)
    (hae : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), HasDerivAt f (f' x) x)
    (hle : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), f' x ≤ g x)
    (hg : IntervalIntegrable g volume a b) :
    f b - f a ≤ ∫ x in a..b, g x := by
  rw [← hac.integral_deriv_eq_sub]
  have hle' : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), deriv f x ≤ g x := by
    have h1 := (ae_restrict_iff' measurableSet_Icc).1 hae
    have h2 := (ae_restrict_iff' measurableSet_Icc).1 hle
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [h1, h2] with x hx1 hx2 hx
    rw [(hx1 hx).deriv]
    exact hx2 hx
  exact intervalIntegral.integral_mono_ae_restrict hab hac.intervalIntegrable_deriv hg hle'



/-! ## Absolute continuity and a.e. differentiability of `r ↦ f r / r ^ c`

The substitution `q r = f r / r ^ c` of Lemma I.4.22 is a smooth (hence absolutely
continuous) reweighting away from `0`, so it preserves absolute continuity and the a.e.
derivative. -/

/-- `r ↦ (r ^ c)⁻¹` is absolutely continuous on a positive window. -/
theorem absolutelyContinuousOnInterval_inv_rpow {c r₀ R : ℝ} (hr₀ : 0 < r₀) (hr₀R : r₀ ≤ R) :
    AbsolutelyContinuousOnInterval (fun r : ℝ => (r ^ c)⁻¹) r₀ R := by
  refine ContDiffOn.absolutelyContinuousOnInterval ?_
  rw [uIcc_of_le hr₀R]
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le hr₀ hx.1
  have hpow : ContDiffAt ℝ 1 (fun r : ℝ => r ^ c) x :=
    Real.contDiffAt_rpow_const_of_ne (x := x) (p := c) (n := 1) hx0.ne'
  exact (ContDiffAt.inv hpow (Real.rpow_pos_of_pos hx0 c).ne').contDiffWithinAt

/-- Dividing an absolutely continuous function by `r ^ c` preserves absolute continuity on a
positive window. -/
theorem AbsolutelyContinuousOnInterval.div_rpow {c r₀ R : ℝ} {f : ℝ → ℝ}
    (hac : AbsolutelyContinuousOnInterval f r₀ R) (hr₀ : 0 < r₀) (hr₀R : r₀ ≤ R) :
    AbsolutelyContinuousOnInterval (fun r => f r / r ^ c) r₀ R := by
  have heq : (fun r : ℝ => f r / r ^ c) = f * fun r : ℝ => (r ^ c)⁻¹ := by
    funext r
    rw [Pi.mul_apply, div_eq_mul_inv]
  rw [heq]
  exact hac.mul (absolutelyContinuousOnInterval_inv_rpow (c := c) hr₀ hr₀R)

/-- A.e. statements on the tail `Ici r₀` restrict to a.e. statements on a window `Icc r₀ R`. -/
theorem ae_restrict_Icc_of_ae_restrict_Ici {p : ℝ → Prop} {r₀ R : ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)), p x) :
    ∀ᵐ x ∂(volume.restrict (Set.Icc r₀ R)), p x :=
  ae_mono (Measure.restrict_mono (fun _ hx => hx.1) le_rfl) h

/-- The quotient rule for `q r = f r / r ^ c`, in the a.e. form needed by the a.e. Lemma I.4.22:
at almost every radius of a set of positive radii,
`q' = (f' r * r - c f r) / r ^ (c + 1)`. -/
theorem ae_hasDerivAt_div_rpow {f f' : ℝ → ℝ} {c : ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hpos : s ⊆ Set.Ioi 0)
    (hae : ∀ᵐ x ∂(volume.restrict s), HasDerivAt f (f' x) x) :
    ∀ᵐ x ∂(volume.restrict s),
      HasDerivAt (fun r => f r / r ^ c) ((f' x * x - c * f x) / x ^ (c + 1)) x := by
  filter_upwards [hae, ae_restrict_mem hs] with x hx hmem
  have hx0 : 0 < x := hpos hmem
  have hp : x ^ c ≠ 0 := (Real.rpow_pos_of_pos hx0 c).ne'
  have hd := HasDerivAt.div hx (Real.hasDerivAt_rpow_const (x := x) (p := c) (Or.inl hx0.ne')) hp
  refine hd.congr_deriv ?_
  have hc1 : x ^ (c + 1) = x ^ c * x := by rw [Real.rpow_add hx0, Real.rpow_one]
  have hc2 : x ^ (c - 1) = x ^ c / x := Real.rpow_sub_one hx0.ne' c
  rw [hc1, hc2]
  field_simp

/-- **The algebraic core of the Lemma I.4.22 comparison.**

At a radius where the one-sided ODE `f' ≤ θ (a f + h)/r` holds, `f > 0` and `a θ ≤ c`, the
derivative of the reweighted function `q r = f r / r ^ c` is bounded by `θ h / r ^ (c+1)`.  This
is the pointwise step of `normalized_increment_le_of_driving_bound`, isolated so that it can be
used at almost every radius. -/
theorem div_rpow_deriv_le_of_driving {f f' θ h : ℝ → ℝ} {a c x : ℝ}
    (hx : 0 < x) (hf : 0 < f x) (hθa : a * θ x ≤ c)
    (hb : f' x ≤ θ x * (a * f x + h x) / x) :
    (f' x * x - c * f x) / x ^ (c + 1) ≤ θ x * h x / x ^ (c + 1) := by
  have hf1 : f' x * x ≤ θ x * (a * f x + h x) := (le_div_iff₀ hx).mp hb
  have he : f' x * x - c * f x ≤ θ x * h x := by
    have hθα : a * θ x * f x ≤ c * f x := mul_le_mul_of_nonneg_right hθa hf.le
    nlinarith
  have hp : 0 < x ^ (c + 1) := Real.rpow_pos_of_pos hx (c + 1)
  exact (div_le_div_iff_of_pos_right hp).2 he

end PercLib.CriticalLRP.Analysis.AE
