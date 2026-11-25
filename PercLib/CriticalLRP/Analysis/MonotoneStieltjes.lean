/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Real-variable structure of a monotone (cutoff-mass) function

For a monotone right-continuous `f : ℝ → ℝ` (bundled as a `StieltjesFunction` `B`) we prove:

* `ae_deriv_eq_rnDeriv_toReal` : the a.e. derivative of `f` is the real form of the
  Radon–Nikodym derivative of the associated Stieltjes measure;
* `ofReal_sub_eq_singularPart_add_lintegral_deriv` : the **Lebesgue decomposition of the
  increment** `f b - f a`, as the mass of the singular part of the Stieltjes measure on
  `(a, b]` plus the integral of the a.e. derivative;
* `lintegral_ofReal_deriv_le_ofReal_sub`, `intervalIntegral_deriv_le_sub` : the unconditional
  inequality `∫ f' ≤ f b - f a` (no moment hypothesis whatsoever);
* `sub_eq_singularPart_toReal_add_intervalIntegral` : the real form of the decomposition;
* `intervalIntegral_deriv_eq_sub_iff_singularPart_eq_zero` : the fundamental theorem of calculus
  for `f` holds on `[a,b]` exactly when the singular (Cantor) part of the Stieltjes measure
  vanishes on `(a,b]`.  This is the sharp form of the remaining "mass transport" input;
* `singularPart_eq_zero_of_absolutelyContinuousOnInterval` : absolute continuity implies that
  vanishing, so the defect in the FTC is exactly the Cantor part.
-/
module

public import Mathlib

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Interval

namespace UltraCriticalLRP

variable {B : StieltjesFunction ℝ}

/-- The a.e. derivative of a Stieltjes function is the real form of its Radon–Nikodym derivative
with respect to Lebesgue measure. -/
theorem ae_deriv_eq_rnDeriv_toReal (B : StieltjesFunction ℝ) :
    deriv (⇑B) =ᵐ[volume] fun x => (B.measure.rnDeriv volume x).toReal := by
  filter_upwards [B.ae_hasDerivAt] with x hx
  exact hx.deriv

/-- On `(a, b]` the integral of `ofReal ∘ f'` is the integral of the Radon–Nikodym derivative. -/
theorem lintegral_ofReal_deriv_eq_lintegral_rnDeriv (B : StieltjesFunction ℝ) (a b : ℝ) :
    ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x)
      = ∫⁻ x in Ioc a b, B.measure.rnDeriv volume x := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mono Measure.restrict_le_self (ae_deriv_eq_rnDeriv_toReal B),
    ae_mono Measure.restrict_le_self (Measure.rnDeriv_lt_top B.measure volume)]
    with x hx hlt
  rw [hx, ENNReal.ofReal_toReal hlt.ne]

/-- The same integral is the mass, under the Stieltjes measure, of its density part. -/
theorem lintegral_ofReal_deriv_eq_withDensity (B : StieltjesFunction ℝ) (a b : ℝ) :
    ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x)
      = (volume.withDensity (B.measure.rnDeriv volume)) (Ioc a b) := by
  rw [withDensity_apply _ measurableSet_Ioc, lintegral_ofReal_deriv_eq_lintegral_rnDeriv]

/-- **Lebesgue decomposition of a monotone increment.**  For a right-continuous monotone
`f = ⇑B` and `a ≤ b`, the increment is the singular (Cantor) part of the Stieltjes measure on
`(a, b]` plus the integral of the a.e. derivative. -/
theorem ofReal_sub_eq_singularPart_add_lintegral_deriv (B : StieltjesFunction ℝ) (a b : ℝ) :
    ENNReal.ofReal (B b - B a)
      = B.measure.singularPart volume (Ioc a b)
        + ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x) := by
  rw [← StieltjesFunction.measure_Ioc B a b]
  conv_lhs => rw [Measure.haveLebesgueDecomposition_add B.measure volume]
  rw [Measure.add_apply, lintegral_ofReal_deriv_eq_withDensity]

/-- **Unconditional integral inequality**: the integral of the a.e. derivative of a monotone
function over `(a, b]` is bounded by the increment. -/
theorem lintegral_ofReal_deriv_le_ofReal_sub (B : StieltjesFunction ℝ) (a b : ℝ) :
    ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x) ≤ ENNReal.ofReal (B b - B a) := by
  rw [ofReal_sub_eq_singularPart_add_lintegral_deriv]
  exact le_add_self

/-- The real integral of the a.e. derivative over `[a, b]` is the `toReal` of its
`ℝ≥0∞`-integral. -/
theorem toReal_lintegral_ofReal_deriv_eq_intervalIntegral (B : StieltjesFunction ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    (∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x)).toReal = ∫ x in a..b, deriv (⇑B) x := by
  rw [intervalIntegral.integral_of_le hab]
  set g : ℝ → ℝ := fun x => (B.measure.rnDeriv volume x).toReal with hg
  have hcongr : ∫ x in Ioc a b, deriv (⇑B) x = ∫ x in Ioc a b, g x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mono Measure.restrict_le_self (ae_deriv_eq_rnDeriv_toReal B)]
      with x hx
    exact hx
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a b)] g := by
    filter_upwards [ae_mono Measure.restrict_le_self (ae_deriv_eq_rnDeriv_toReal B)]
      with x hx
    rw [show g x = (B.measure.rnDeriv volume x).toReal from rfl, ← hx]
    exact B.mono.deriv_nonneg
  have hmeas : AEStronglyMeasurable g (volume.restrict (Ioc a b)) :=
    (Measure.measurable_rnDeriv B.measure volume).ennreal_toReal.aestronglyMeasurable
  have hkey : ∫⁻ x in Ioc a b, ENNReal.ofReal (g x)
      = ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mono Measure.restrict_le_self (ae_deriv_eq_rnDeriv_toReal B)]
      with x hx
    rw [show g x = (B.measure.rnDeriv volume x).toReal from rfl, ← hx]
  rw [hcongr, integral_eq_lintegral_of_nonneg_ae hnn hmeas, hkey]

/-- The real-valued interval form of the unconditional inequality `∫ f' ≤ f b - f a`. -/
theorem intervalIntegral_deriv_le_sub (B : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, deriv (⇑B) x ≤ B b - B a := by
  rw [← toReal_lintegral_ofReal_deriv_eq_intervalIntegral B hab]
  calc (∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x)).toReal
      ≤ (ENNReal.ofReal (B b - B a)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_ofReal_deriv_le_ofReal_sub B a b)
    _ = B b - B a := ENNReal.toReal_ofReal (sub_nonneg.mpr (B.mono hab))

/-- The `ℝ≥0∞`-integral of `ofReal ∘ f'` is never `⊤` on a finite increment window. -/
theorem lintegral_ofReal_deriv_ne_top (B : StieltjesFunction ℝ) (a b : ℝ) :
    (∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x)) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_ofReal_deriv_le_ofReal_sub B a b)

/-- The singular part of the Stieltjes measure is finite on a finite increment window. -/
theorem singularPart_ne_top (B : StieltjesFunction ℝ) (a b : ℝ) :
    B.measure.singularPart volume (Ioc a b) ≠ ⊤ := by
  have hle : B.measure.singularPart volume (Ioc a b) ≤ ENNReal.ofReal (B b - B a) := by
    rw [ofReal_sub_eq_singularPart_add_lintegral_deriv B a b, add_comm]
    exact le_add_self
  exact ne_top_of_le_ne_top (a := B.measure.singularPart volume (Ioc a b))
    ENNReal.ofReal_ne_top hle

/-- **Real form of the Lebesgue decomposition**: the increment is the Cantor part plus the
integral of the a.e. derivative. -/
theorem sub_eq_singularPart_toReal_add_intervalIntegral (B : StieltjesFunction ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    B b - B a
      = (B.measure.singularPart volume (Ioc a b)).toReal + ∫ x in a..b, deriv (⇑B) x := by
  have hdec := ofReal_sub_eq_singularPart_add_lintegral_deriv B a b
  have h := congrArg ENNReal.toReal hdec
  rw [ENNReal.toReal_add (singularPart_ne_top B a b) (lintegral_ofReal_deriv_ne_top B a b),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (B.mono hab)),
    toReal_lintegral_ofReal_deriv_eq_intervalIntegral B hab] at h
  exact h

/-- **The FTC criterion**: the fundamental theorem of calculus `∫ f' = f b - f a` holds on
`[a, b]` exactly when the singular part of the Stieltjes measure vanishes on `(a, b]`. -/
theorem intervalIntegral_deriv_eq_sub_iff_singularPart_eq_zero (B : StieltjesFunction ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ x in a..b, deriv (⇑B) x = B b - B a
      ↔ B.measure.singularPart volume (Ioc a b) = 0 := by
  constructor
  · intro h
    have hdec := sub_eq_singularPart_toReal_add_intervalIntegral B hab
    rw [h, add_comm] at hdec
    have h0 : (B.measure.singularPart volume (Ioc a b)).toReal = 0 := by linarith
    by_contra hne
    have hpos : 0 < (B.measure.singularPart volume (Ioc a b)).toReal :=
      ENNReal.toReal_pos hne (singularPart_ne_top B a b)
    linarith
  · intro h
    have hdec := sub_eq_singularPart_toReal_add_intervalIntegral B hab
    rw [h] at hdec
    simp only [ENNReal.toReal_zero, zero_add] at hdec
    exact hdec.symm

/-- **Absolute continuity kills the Cantor part**, hence forces the FTC on the window. -/
theorem singularPart_eq_zero_of_absolutelyContinuousOnInterval (B : StieltjesFunction ℝ)
    {a b : ℝ} (hab : a ≤ b) (h : AbsolutelyContinuousOnInterval (⇑B) a b) :
    B.measure.singularPart volume (Ioc a b) = 0 := by
  have hdec := ofReal_sub_eq_singularPart_add_lintegral_deriv B a b
  have hInt : ∫ x in a..b, deriv (⇑B) x = B b - B a := h.integral_deriv_eq_sub
  have hto : (∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x)) = ENNReal.ofReal (B b - B a) := by
    rw [← ENNReal.ofReal_toReal (lintegral_ofReal_deriv_ne_top B a b),
      toReal_lintegral_ofReal_deriv_eq_intervalIntegral B hab, hInt]
  have h4 : B.measure.singularPart volume (Ioc a b)
        + ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x)
      = ∫⁻ x in Ioc a b, ENNReal.ofReal (deriv (⇑B) x) := by
    rw [← hdec, hto]
  refine (ENNReal.add_left_inj (lintegral_ofReal_deriv_ne_top B a b)).mp ?_
  rw [zero_add]
  exact h4

end UltraCriticalLRP
