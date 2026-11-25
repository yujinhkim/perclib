/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
**The Tauberian layer of Theorem I.2.11** (Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1, p. 26, citing Feller XIII.5.2).

Theorem I.2.11 of the paper states: for `f` regularly varying of index `-α` with
`0 ≤ α < 1` and `X ≥ 0` a nonnegative random variable,

  `E[1 - e^{-hX}] ~ f(1/h)` as `h ↓ 0`   **iff**   `P(X ≥ x) ~ f(x)/Γ(1-α)` as `x → ∞`.

This file formalises, sorry-free and with only the standard axioms
(`propext, Classical.choice, Quot.sound`):

* the **Laplace–tail identity** `E_μ[1 - e^{-hX}] = h ∫_0^∞ e^{-hx} μ((x,∞)) dx`
  for a probability measure `μ` on `[0,∞)` and `h > 0`
  (`integral_one_sub_exp_eq_laplace_tail`);
* the **Abelian direction** of the theorem
  (`laplace_tail_asymptotic_of_tail`): if the tail is asymptotic to
  `f(x)/Γ(1-α)` with `f` regularly varying of index `-α`, `α < 1`, then
  `E_μ[1 - e^{-hX}] ~ f(1/h)`.  The exact constant `Γ(1-α)` enters through
  `Gamma_one_sub_eq_integral : Γ(1-α) = ∫_0^∞ e^{-u}u^{-α}du`, and the proof
  uses Potter's bounds (derived from regular variation in
  `Analysis/UniformConvergence`) and dominated convergence on the rescaled
  integral `∫_0^∞ e^{-u}F(u/h)du`.

* The probabilistic `laplace_tail_asymptotic_of_tail` uses the strict tail event
  `P(X > x)`. The source writes `P(X ≥ x)`; that routine asymptotic-equivalence
  bridge is not silently asserted in this module.

The Tauberian converse (Laplace asymptotics imply tail asymptotics) is proved in
`Analysis/TauberianConverseComplete.lean`. This module supplies the Laplace--tail
identities and the Abelian direction used by that completed equivalence. The
percolation application in the paper's Proposition I.3.2 remains separate.
-/
module

public import PercLib.CriticalLRP.Analysis.UniformConvergence

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.Analysis

/-! ### The Gamma integral -/

/-- The Gamma integral in the form used below: `Γ(1-α) = ∫_0^∞ e^{-u} u^{-α} du`
for `α < 1`. -/
theorem Gamma_one_sub_eq_integral {α : ℝ} (hα : α < 1) :
    Real.Gamma (1 - α) = ∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * u ^ (-α) := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 1) (q := -α) one_pos (by linarith : (-1:ℝ) < -α)
  have h' : Real.Gamma (1 - α) = ∫ x in Set.Ioi (0 : ℝ), x ^ (-α) * Real.exp (-x) := by
    have hh := h.symm
    simp only [Real.rpow_one, div_one, one_mul] at hh
    rw [show -α + (1:ℝ) = 1 - α from by ring] at hh
    exact hh
  rw [h']
  exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => mul_comm _ _)

/-- **`h / f(1/h) → 0` for `f` regularly varying of index `-α`, `α < 1`.**  This is the
elementary consequence of the lower Potter bound that makes the small-`u` region of the
rescaled Laplace integral negligible. -/
theorem tendsto_div_of_regularlyVarying_neg {f : ℝ → ℝ} {α : ℝ} (hα : α < 1)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α)) :
    Tendsto (fun h : ℝ => h / f (1/h)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ α + η < 1 ∧ η ≤ 1/2 := by
    refine ⟨min (1/2) ((1 - α)/2), lt_min (by norm_num) (by linarith), ?_, min_le_left _ _⟩
    calc α + min (1/2) ((1 - α)/2) ≤ α + (1 - α)/2 := by linarith [min_le_right (1/2) ((1-α)/2)]
      _ < 1 := by linarith
  obtain ⟨X₁, hX₁le, hX₁⟩ := hasPotterBounds_of_regularlyVarying hfmeas hrv η hη0
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.1 hrv.1
  set Y := max Y₀ X₁ with hYdef
  have hY₀' : Y₀ ≤ Y := le_max_left _ _
  have hX₁Y : X₁ ≤ Y := le_max_right _ _
  have hYpos : 0 < Y := lt_of_lt_of_le (by linarith : (0:ℝ) < 1) (le_trans hX₁le hX₁Y)
  have hfY : f Y ≠ 0 := hY₀ Y hY₀'
  have hbound : ∀ h : ℝ, 0 < h → h ≤ 1 / Y → (1 - η) * (Y * h) ^ (α + η) * |f Y| ≤ |f (1/h)| := by
    intro h hh hle
    have hxy : Y ≤ 1 / h := by
      rw [le_div_iff₀ hh]
      have h3 : h * Y ≤ 1 := by
        have h4 := mul_le_mul_of_nonneg_right hle hYpos.le
        have h5 : (1:ℝ)/Y * Y = 1 := by field_simp
        linarith [h4, h5]
      linarith
    have hkey := potter_lower (f := f) (α := -α) (ε := η) (X := X₁) hX₁ (x := 1/h) (y := Y)
      hX₁Y hxy
    have hpow : ((1/h) / Y) ^ (-α - η) = (Y * h) ^ (α + η) := by
      have hp : (0:ℝ) ≤ Y * h := (mul_pos hYpos hh).le
      have e1 : (1/h) / Y = (Y * h)⁻¹ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_inv_rev]
      rw [e1, ← Real.rpow_neg_one (Y * h), ← Real.rpow_mul hp,
        show (-1) * (-α - η) = (α + η) from by ring]
    rw [hpow] at hkey
    exact hkey
  set c : ℝ := (1 - η) * Y ^ (α + η) * |f Y| with hcdef
  have hcpos : 0 < c :=
    mul_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hYpos _)) (abs_pos.2 hfY)
  have hleY : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), h ≤ 1 / Y :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_lt_nhds (show (0:ℝ) < 1 / Y by positivity)) |>.mono (fun h hh => hh.le)
  have hsq : ∀ᶠ h in 𝓝[>] (0 : ℝ), ‖h / f (1/h)‖ ≤ (1/c) * h ^ (1 - α - η) := by
    filter_upwards [self_mem_nhdsWithin, hleY] with h hh0 hhle
    have hb := hbound h hh0 hhle
    have h2 : (Y * h) ^ (α + η) = Y ^ (α + η) * h ^ (α + η) := Real.mul_rpow hYpos.le hh0.le
    rw [h2] at hb
    have h1 : c * h ^ (α + η) ≤ |f (1/h)| := by
      rw [hcdef]
      calc (1 - η) * Y ^ (α + η) * |f Y| * h ^ (α + η)
          = (1 - η) * (Y ^ (α + η) * h ^ (α + η)) * |f Y| := by ring
        _ ≤ |f (1/h)| := hb
    have h4 : h / (c * h ^ (α + η)) = (1/c) * h ^ (1 - α - η) := by
      have hden : c * h ^ (α + η) ≠ 0 :=
        ne_of_gt (mul_pos hcpos (Real.rpow_pos_of_pos hh0 _))
      rw [div_eq_iff hden]
      have kk : (1/c) * h ^ (1 - α - η) * (c * h ^ (α + η))
          = h ^ (1 - α - η) * h ^ (α + η) := by
        field_simp
      rw [kk, ← Real.rpow_add hh0, show 1 - α - η + (α + η) = 1 from by ring, Real.rpow_one]
    have hA : 0 < c * h ^ (α + η) := mul_pos hcpos (Real.rpow_pos_of_pos hh0 _)
    calc ‖h / f (1/h)‖ = h / |f (1/h)| := by
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hh0]
      _ ≤ h / (c * h ^ (α + η)) := div_le_div_of_nonneg_left hh0.le hA h1
      _ = (1/c) * h ^ (1 - α - η) := h4
  have hlim : Tendsto (fun h : ℝ => (1/c) * h ^ (1 - α - η)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun h : ℝ => h ^ (-(1 - α - η))) (𝓝[>] (0:ℝ)) atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith : -(1 - α - η) < 0)
    have h2 : Tendsto (fun h : ℝ => (h ^ (-(1 - α - η)))⁻¹) (𝓝[>] (0:ℝ)) (𝓝 0) :=
      h1.inv_tendsto_atTop
    have h3 : Tendsto (fun h : ℝ => (1/c) * (h ^ (-(1 - α - η)))⁻¹) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using h2.const_mul (1/c)
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [Real.rpow_neg hh.le, inv_inv]
  have hnorm : Tendsto (fun h : ℝ => ‖h / f (1/h)‖) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun h => norm_nonneg _)) hsq hlim
  exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm

/-- Pointwise bound: under Potter's bounds, for `u ≥ h Y` the ratio
`f (u/h) / f (1/h)` is at most `B (u^{-α-η} + u^{-α+η})`. -/
theorem rv_ratio_bound {f : ℝ → ℝ} {α η X₁ Y B h : ℝ}
    (hpot : ∀ x y : ℝ, X₁ ≤ y → y ≤ x →
      (1 - η) * (x / y) ^ (-α - η) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + η) * (x / y) ^ (-α + η) * |f y|)
    (hα0 : 0 ≤ α) (hη0 : 0 < η) (hη1 : η < 1)
    (hX₁pos : 0 < X₁) (hX₁Y : X₁ ≤ Y) (hYpos : 0 < Y) (hB : B = max (1 + η) (1/(1 - η)))
    (hhu : 0 < h) (hX1 : X₁ ≤ 1/h)
    (hposinv : 0 < f (1/h))
    (hpos : ∀ u : ℝ, h * Y ≤ u → 0 < f (u/h)) :
    ∀ u : ℝ, h * Y ≤ u → f (u/h) ≤ B * (u ^ (-α - η) + u ^ (-α + η)) * f (1/h) := by
  intro u hu
  have hxX₁ : X₁ ≤ u/h := by
    rw [le_div_iff₀ hhu]
    have h1 : h * X₁ ≤ h * Y := by nlinarith
    linarith
  have hposx : 0 < f (u/h) := hpos u hu
  have hposu : (0:ℝ) < u := lt_of_lt_of_le (mul_pos hhu hYpos) hu
  have hαη : (0:ℝ) < 1 - η := by linarith
  have hBle : (1 + η) ≤ B := by rw [hB]; exact le_max_left _ _
  have hBle' : 1/(1-η) ≤ B := by rw [hB]; exact le_max_right _ _
  have hBpos : (0:ℝ) < B := lt_of_lt_of_le (by linarith : (0:ℝ) < 1 + η) hBle
  rcases le_or_gt (1:ℝ) u with hu1 | hu1
  · have hxy : 1/h ≤ u/h := by rw [div_le_div_iff_of_pos_right hhu]; linarith
    have hb := (hpot (u/h) (1/h) hX1 hxy).2
    have hpow : ((u/h)/(1/h)) ^ (-α + η) = u ^ (-α + η) := by
      have h1 : (u/h)/(1/h) = u := by field_simp
      rw [h1]
    rw [hpow, abs_of_pos hposx, abs_of_pos hposinv] at hb
    have hkey : u ^ (-α + η) ≤ u ^ (-α - η) + u ^ (-α + η) := le_add_of_nonneg_left (by positivity)
    calc f (u/h) ≤ (1 + η) * u ^ (-α + η) * f (1/h) := hb
      _ ≤ B * (u ^ (-α - η) + u ^ (-α + η)) * f (1/h) := by
          have h1 : (1 + η) * u ^ (-α + η) ≤ B * (u ^ (-α - η) + u ^ (-α + η)) := by
            have h2 : (1+η) * u ^ (-α + η) ≤ B * u ^ (-α + η) :=
              mul_le_mul_of_nonneg_right hBle (by positivity)
            have h3 : B * u ^ (-α + η) ≤ B * (u ^ (-α - η) + u ^ (-α + η)) :=
              mul_le_mul_of_nonneg_left hkey hBpos.le
            linarith
          exact mul_le_mul_of_nonneg_right h1 hposinv.le
  · have huy : u/h ≤ 1/h := by rw [div_le_div_iff_of_pos_right hhu]; linarith
    have hb := (hpot (1/h) (u/h) hxX₁ huy).1
    have hpow : ((1/h)/(u/h)) ^ (-α - η) = u ^ (α + η) := by
      have h1 : (1/h)/(u/h) = u ^ (-1:ℝ) := by
        rw [Real.rpow_neg_one]; field_simp
      rw [h1, ← Real.rpow_mul hposu.le, show (-1:ℝ) * (-α - η) = α + η from by ring]
    rw [hpow, abs_of_pos hposinv, abs_of_pos hposx] at hb
    have hcoef : (0:ℝ) < (1 - η) * u ^ (α + η) := by positivity
    have h2 : f (1/h) / ((1 - η) * u ^ (α + η)) = (1/(1-η)) * u ^ (-α - η) * f (1/h) := by
      rw [show -α - η = -(α + η) from by ring, Real.rpow_neg hposu.le]
      field_simp
    have h1 : f (u/h) ≤ (1/(1-η)) * u ^ (-α - η) * f (1/h) := by
      rw [← h2, le_div_iff₀ hcoef, mul_comm]
      exact hb
    have h4 : (1/(1-η)) * u ^ (-α - η) ≤ B * u ^ (-α - η) :=
      mul_le_mul_of_nonneg_right hBle' (by positivity)
    have h5 : u ^ (-α - η) ≤ u ^ (-α - η) + u ^ (-α + η) := le_add_of_nonneg_right (by positivity)
    calc f (u/h) ≤ (1/(1-η)) * u ^ (-α - η) * f (1/h) := h1
      _ ≤ B * u ^ (-α - η) * f (1/h) := mul_le_mul_of_nonneg_right h4 hposinv.le
      _ ≤ B * (u ^ (-α - η) + u ^ (-α + η)) * f (1/h) := by
          have h6 : B * u ^ (-α - η) ≤ B * (u ^ (-α - η) + u ^ (-α + η)) :=
            mul_le_mul_of_nonneg_left h5 hBpos.le
          exact mul_le_mul_of_nonneg_right h6 hposinv.le

/-- Integrability of `u ↦ e^{-u} u^q` on `(0,∞)` for `q > -1`. -/
theorem integrableOn_exp_mul_rpow {q : ℝ} (hq : -1 < q) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ q) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := q) hq one_pos
  simpa [Real.rpow_one, mul_comm] using h

/-- **Pointwise limit of the rescaled ratio**: for fixed `u > 0`,
`f (u/h) / f (1/h) → u^{-α}` as `h ↓ 0`. -/
theorem tendsto_rv_ratio {f : ℝ → ℝ} {α u : ℝ} (hu : 0 < u)
    (hrv : RegularlyVaryingAtTop f (-α)) :
    Tendsto (fun h : ℝ => f (u/h) / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 (u ^ (-α))) := by
  have h1 : Tendsto (fun h : ℝ => 1/h) (𝓝[>] (0:ℝ)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  have h2 := hrv.2 u hu |>.comp h1
  refine h2.congr' ?_
  filter_upwards with h
  simp only [Function.comp_apply, mul_one_div]

/-- **Pointwise limit of the rescaled ratio, second form**: for fixed `u > 0`,
`Γ F(u/h)/f(u/h) → 1` along the tail hypothesis. -/
theorem tendsto_ratio_F {F f : ℝ → ℝ} {α u : ℝ} (hαpos : 0 < 1 - α) (hu : 0 < u)
    (htail : Tendsto (fun x => F x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => Real.Gamma (1 - α) * F (u/h) / f (u/h)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have h1 : Tendsto (fun h : ℝ => u/h) (𝓝[>] (0:ℝ)) atTop := by
    have := Tendsto.const_mul_atTop hu tendsto_inv_nhdsGT_zero
    simpa [div_eq_mul_inv] using this
  have h2 := htail.comp h1
  refine h2.congr' ?_
  filter_upwards [h1.eventually (eventually_ne_atTop 0)] with h hne
  have hΓ : Real.Gamma (1 - α) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hαpos)
  simp only [Function.comp_apply]
  field_simp
/-! ### The Laplace–tail identity -/

/-- `1 - e^{-h s} = ∫_0^∞ 1{x < s} · h e^{-h x} dx` for `s ≥ 0`. -/
theorem one_sub_exp_eq_setIntegral_indicator {h s : ℝ} (hs : 0 ≤ s) :
    ∫ x in Set.Ioi (0 : ℝ), (Set.Iio s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x
      = 1 - Real.exp (-(h * s)) := by
  rw [← neg_mul]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) s,
      HasDerivAt (fun x : ℝ => -Real.exp (-h * x)) (h * Real.exp (-h * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -h * x) (-h) x := by
      simpa using (hasDerivAt_id x).const_mul (-h)
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-h * x)) (Real.exp (-h * x) * (-h)) x := h1.exp
    have h3 : HasDerivAt (fun x : ℝ => -Real.exp (-h * x)) (-(Real.exp (-h * x) * (-h))) x :=
      h2.neg
    convert h3 using 1
    ring
  have hint : IntervalIntegrable (fun x : ℝ => h * Real.exp (-h * x)) volume 0 s :=
    ((continuous_const.mul (Real.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ => -h * x)))).intervalIntegrable _ _
  have hclosed := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hmain : ∫ x in (0 : ℝ)..s, h * Real.exp (-h * x) = 1 - Real.exp (-h * s) := by
    rw [hclosed]
    have h0 : Real.exp (-h * 0) = 1 := by simp
    rw [h0]; ring
  rw [← hmain, intervalIntegral.integral_of_le hs,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    show Set.Ioo (0 : ℝ) s = Set.Ioi 0 ∩ Set.Iio s from rfl,
    ← MeasureTheory.setIntegral_indicator measurableSet_Iio]
  simp only [neg_mul]

/-- **The Laplace–tail identity.**  For a probability measure `μ` on `ℝ` carried by
`[0,∞)` and `h > 0`,

  `E_μ[1 - e^{-h X}] = h ∫_0^∞ e^{-h x} μ((x,∞)) dx`.

This is the identity behind the probabilistic formulation of Karamata's Tauberian
theorem (Feller XIII.5.2; Hutchcroft, Theorem I.2.11): the left side is the
Laplace transform of the *tail*, written in "`1 - φ(h)`" form. -/
theorem integral_one_sub_exp_eq_laplace_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) {h : ℝ} (hh : 0 < h) :
    ∫ s, (1 - Real.exp (-(h * s))) ∂μ
      = h * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(h * x)) * (μ (Set.Ioi x)).toReal := by
  classical
  have hae : ∀ᵐ s ∂μ, 0 ≤ s := by
    rw [MeasureTheory.ae_iff]
    convert hμ using 2
    ext x
    simp
  have hstep1 : ∫ s, (1 - Real.exp (-(h * s))) ∂μ
      = ∫ s, ∫ x in Set.Ioi (0 : ℝ),
          (Set.Iio s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x ∂volume ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with s hs
    exact (one_sub_exp_eq_setIntegral_indicator hs).symm
  have hmaj : Integrable (fun z : ℝ × ℝ => h * Real.exp (-(h * z.2)))
      (μ.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const _
    have h2 : Integrable (fun x : ℝ => h * Real.exp (-h * x)) (volume.restrict (Set.Ioi 0)) :=
      (integrableOn_exp_mul_Ioi (by linarith : -h < 0) 0).const_mul h
    have h3 := h1.mul_prod h2
    have h4 : (fun z : ℝ × ℝ => (1:ℝ) * (h * Real.exp (-h * z.2)))
        = fun z : ℝ × ℝ => h * Real.exp (-(h * z.2)) := by
      ext z; rw [one_mul, neg_mul]
    rw [h4] at h3
    exact h3
  have hmeas : Measurable fun p : ℝ × ℝ =>
      (Set.Iio p.1).indicator (fun x : ℝ => h * Real.exp (-(h * x))) p.2 := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
      measurableSet_lt measurable_snd measurable_fst
    have hfun : Measurable fun p : ℝ × ℝ => h * Real.exp (-(h * p.2)) :=
      measurable_const.mul (Real.measurable_exp.comp ((measurable_const.mul measurable_snd).neg))
    exact hfun.indicator hset
  have hjoint : Integrable (Function.uncurry fun s x : ℝ =>
      (Set.Iio s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x)
      (μ.prod (volume.restrict (Ioi 0))) := by
    refine hmaj.mono hmeas.aestronglyMeasurable ?_
    filter_upwards with p
    obtain ⟨s, x⟩ := p
    simp only [Function.uncurry_apply_pair]
    rw [Set.indicator_apply]
    split_ifs with hxs
    · simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hh, Real.abs_exp]
      exact le_rfl
    · simp only [norm_zero]
      positivity
  rw [hstep1, integral_integral_swap hjoint]
  have hinner : ∀ x : ℝ, ∫ s, (Set.Iio s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x ∂μ
      = h * Real.exp (-(h * x)) * (μ (Set.Ioi x)).toReal := by
    intro x
    have hfun : ∀ s : ℝ, (Set.Iio s).indicator (fun x : ℝ => h * Real.exp (-(h * x))) x
        = h * Real.exp (-(h * x)) * (Set.Ioi x).indicator (fun _ => (1:ℝ)) s := by
      intro s
      simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ioi]
      split_ifs with h1 <;> ring
    have h1 : ∀ x : ℝ, ∫ s, h * Real.exp (-(h * x)) * (Set.Ioi x).indicator (fun _ => (1:ℝ)) s ∂μ
        = h * Real.exp (-(h * x)) * (μ (Set.Ioi x)).toReal := by
      intro x
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator_const (1:ℝ) measurableSet_Ioi, Measure.real]
      simp
    simp only [hfun, h1]
  simp only [hinner]
  rw [← integral_const_mul]
  ring_nf


/-! ### The Abelian direction of Theorem I.2.11 -/

/-- **Tail asymptotics imply Laplace asymptotics** (Feller XIII.5.2, the easy
direction of Karamata's Tauberian theorem; Hutchcroft Theorem I.2.11).

Let `F ≥ 0` be bounded and measurable with `F(x) ~ f(x)/Γ(1-α)` as `x → ∞`, where
`f` is regularly varying of index `-α`, `α < 1`.  Then

  `h ∫_0^∞ e^{-hx} F(x) dx ~ f(1/h)`   as `h ↓ 0`,

with the exact constant `Γ(1-α)` entering through `f/Γ(1-α)`. The converse,
Laplace asymptotics ⟹ tail asymptotics, is proved in
`Analysis/TauberianConverseComplete.lean`. -/
theorem tendsto_laplace_of_tail_asymptotic
    {F f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hFmeas : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (htail : Tendsto (fun x => F x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => (h * ∫ x in Set.Ioi (0:ℝ), Real.exp (-(h*x)) * F x) / f (1/h))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  classical
  have hαpos : (0:ℝ) < 1 - α := by linarith
  have hΓpos : (0:ℝ) < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos hαpos
  -- ### Step 1: the rescaled form
  have hsub : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
      h * (∫ x in Set.Ioi (0:ℝ), Real.exp (-(h*x)) * F x)
        = ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * F (u/h) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := ne_of_gt hh
    have hcomp := integral_comp_mul_left_Ioi (fun u : ℝ => Real.exp (-u) * F (u/h)) (0:ℝ) hh
    simp only [smul_eq_mul, mul_zero] at hcomp
    have hfun : (fun x : ℝ => Real.exp (-(h*x)) * F (h*x/h))
        = fun x : ℝ => Real.exp (-(h*x)) * F x := by
      ext x; rw [mul_div_cancel_left₀ x hh0]
    rw [hfun] at hcomp
    rw [hcomp, ← mul_assoc, mul_inv_cancel₀ hh0, one_mul]
  refine (show Tendsto (fun h : ℝ => (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h))
      (𝓝[>] (0:ℝ)) (𝓝 1) from ?_).congr' ?_
  · -- ### Step 2: the rescaled assertion
    obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ α + η < 1 ∧ η < 1 := by
      refine ⟨min ((1 - α)/2) (1/2), lt_min (by linarith) (by norm_num), ?_, ?_⟩
      · have h := min_le_left ((1 - α)/2) (1/2); linarith
      · have h := min_le_right ((1 - α)/2) (1/2); linarith
    obtain ⟨X₁, hX₁le, hpot⟩ := hasPotterBounds_of_regularlyVarying hfmeas hrv η hη0
    have hX₁pos : (0:ℝ) < X₁ := lt_of_lt_of_le one_pos hX₁le
    have hratio_ev : ∀ᶠ x in atTop, |Real.Gamma (1 - α) * F x / f x - 1| ≤ η := by
      have hlt : ∀ᶠ x in atTop, F x / (f x / Real.Gamma (1 - α)) < 1 + η :=
        htail.eventually (eventually_lt_nhds (by linarith))
      have hgt : ∀ᶠ x in atTop, 1 - η < F x / (f x / Real.Gamma (1 - α)) :=
        htail.eventually (eventually_gt_nhds (by linarith : 1 - η < 1))
      filter_upwards [hlt, hgt] with x hx1 hx2
      have hΓne : Real.Gamma (1 - α) ≠ 0 := ne_of_gt hΓpos
      have hdiv : F x / (f x / Real.Gamma (1 - α)) = Real.Gamma (1 - α) * F x / f x := by
        rw [div_div_eq_mul_div, mul_comm]
      rw [hdiv] at hx1 hx2
      rw [abs_le]
      constructor <;> linarith
    have hposf_ev : ∀ᶠ x in atTop, 0 < f x := by
      filter_upwards [hratio_ev] with x hx
      by_contra hcon
      push Not at hcon
      have hx' : Real.Gamma (1 - α) * F x / f x ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (mul_nonneg hΓpos.le (hF0 x)) hcon
      have : |Real.Gamma (1 - α) * F x / f x - 1| ≥ 1 := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - Real.Gamma (1 - α) * F x / f x)]
        linarith
      linarith
    have hFeq_ev : ∀ᶠ x in atTop, |Real.Gamma (1 - α) * F x - f x| ≤ η * f x := by
      filter_upwards [hratio_ev, hposf_ev] with x hx hpos
      have h1 : Real.Gamma (1 - α) * F x / f x - 1 = (Real.Gamma (1 - α) * F x - f x) / f x := by
        field_simp
      rw [h1, abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at hx
      linarith [hx]
    obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 (hFeq_ev.and hposf_ev)
    set X : ℝ := max X₁ X₂ with hXdef
    have hX1 : 1 ≤ X := le_trans hX₁le (le_max_left _ _)
    have hXpos : (0:ℝ) < X := lt_of_lt_of_le one_pos hX1
    have hX₁X : X₁ ≤ X := le_max_left _ _
    have hX₂X : X₂ ≤ X := le_max_right _ _
    set B : ℝ := max (1 + η) (1/(1 - η)) with hBdef
    have hBpos : 0 < B := lt_of_lt_of_le (by linarith : (0:ℝ) < 1 + η) (le_max_left _ _)
    -- the pointwise bound
    have hkey : ∀ h : ℝ, 0 < h → h ≤ 1/X → ∀ u : ℝ, h * X ≤ u →
        |(Real.Gamma (1 - α) / f (1/h)) * F (u / h) - u ^ (-α)| ≤
          (1 + η) * B * (u ^ (-α - η) + u ^ (-α + η)) + u ^ (-α) := by
      intro h hh hle u hu
      have hxX : X ≤ u / h := by rw [le_div_iff₀ hh]; linarith
      have hxX₂ : X₂ ≤ u / h := le_trans hX₂X hxX
      obtain ⟨hFeqx, hposfx⟩ := hX₂ (u/h) hxX₂
      have hinvX : X ≤ 1/h := by
        rw [le_div_iff₀ hh]
        have h1 : h * X ≤ 1 := by
          have h2 := mul_le_mul_of_nonneg_right hle hXpos.le
          rwa [one_div, inv_mul_cancel₀ (ne_of_gt hXpos)] at h2
        linarith
      have hposinv : 0 < f (1/h) := (hX₂ (1/h) (le_trans hX₂X hinvX)).2
      have hpos : ∀ u' : ℝ, h * X ≤ u' → 0 < f (u'/h) := by
        intro u' hu'
        apply (hX₂ (u'/h) (le_trans hX₂X ?_)).2
        rw [le_div_iff₀ hh]
        linarith
      have hrb := rv_ratio_bound (f := f) hpot hα0 hη0 hη2 hX₁pos hX₁X hXpos hBdef.symm hh
        (le_trans hX₁X hinvX) hposinv hpos u hu
      have hsplit : (Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α)
          = (Real.Gamma (1 - α) * F (u/h) - f (u/h)) / f (1/h)
            + (f (u/h) / f (1/h) - u ^ (-α)) := by
        field_simp
        ring
      rw [hsplit]
      have hb1 : |(Real.Gamma (1 - α) * F (u/h) - f (u/h)) / f (1/h)| ≤ η * (f (u/h) / f (1/h)) := by
        rw [abs_div, abs_of_pos hposinv, div_le_iff₀ hposinv]
        have he : η * (f (u/h) / f (1/h)) * f (1/h) = η * f (u/h) := by field_simp
        rw [he]
        exact hFeqx
      have hb2 : |f (u/h) / f (1/h) - u ^ (-α)| ≤ f (u/h) / f (1/h) + u ^ (-α) := by
        have h1 : 0 ≤ f (u/h) / f (1/h) := le_of_lt (div_pos hposfx hposinv)
        have h2 : 0 ≤ u ^ (-α) := le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le (mul_pos hh hXpos) hu) _)
        rw [abs_le]
        constructor <;> linarith
      have hrb' : f (u/h) / f (1/h) ≤ B * (u ^ (-α - η) + u ^ (-α + η)) := by
        rw [div_le_iff₀ hposinv]
        calc f (u/h) ≤ B * (u ^ (-α - η) + u ^ (-α + η)) * f (1/h) := hrb
          _ = (B * (u ^ (-α - η) + u ^ (-α + η))) * f (1/h) := by ring
      have hb3 : (1 + η) * (f (u/h) / f (1/h)) ≤ (1 + η) * (B * (u ^ (-α - η) + u ^ (-α + η))) :=
        mul_le_mul_of_nonneg_left hrb' (by linarith)
      calc |(Real.Gamma (1 - α) * F (u/h) - f (u/h)) / f (1/h)
            + (f (u/h) / f (1/h) - u ^ (-α))|
          ≤ |(Real.Gamma (1 - α) * F (u/h) - f (u/h)) / f (1/h)|
            + |f (u/h) / f (1/h) - u ^ (-α)| := abs_add_le _ _
        _ ≤ η * (f (u/h) / f (1/h)) + (f (u/h) / f (1/h) + u ^ (-α)) := by linarith
        _ = (1 + η) * (f (u/h) / f (1/h)) + u ^ (-α) := by ring
        _ ≤ (1 + η) * (B * (u ^ (-α - η) + u ^ (-α + η))) + u ^ (-α) := by linarith [hb3]
        _ = (1 + η) * B * (u ^ (-α - η) + u ^ (-α + η)) + u ^ (-α) := by ring
    have hmeasind : ∀ h : ℝ, Measurable fun u : ℝ =>
        (Set.Ici (h*X)).indicator (fun u => Real.exp (-u) *
          ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α))) u := by
      intro h
      have hinner : Measurable fun u : ℝ =>
          Real.exp (-u) * ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α)) := by
        refine Measurable.mul ((Real.measurable_exp.comp measurable_id.neg)) ?_
        refine Measurable.sub (Measurable.mul measurable_const ?_) ?_
        · exact hFmeas.comp (measurable_id.div_const h)
        · exact (by fun_prop : Measurable fun u : ℝ => u ^ (-α))
      exact hinner.indicator measurableSet_Ici
    -- ### Step 3: the majorant and the integrability statements
    have hb1 : Integrable (fun u : ℝ => Real.exp (-u) * u ^ (-α - η))
        (volume.restrict (Set.Ioi 0)) :=
      integrableOn_exp_mul_rpow (by linarith : (-1:ℝ) < -α - η)
    have hb2 : Integrable (fun u : ℝ => Real.exp (-u) * u ^ (-α + η))
        (volume.restrict (Set.Ioi 0)) :=
      integrableOn_exp_mul_rpow (by linarith : (-1:ℝ) < -α + η)
    have hb3 : Integrable (fun u : ℝ => Real.exp (-u) * u ^ (-α))
        (volume.restrict (Set.Ioi 0)) :=
      integrableOn_exp_mul_rpow (by linarith : (-1:ℝ) < -α)
    have hmaj : Integrable (fun u : ℝ => Real.exp (-u) *
        ((1 + η) * B * (u ^ (-α - η) + u ^ (-α + η)) + u ^ (-α)))
        (volume.restrict (Set.Ioi 0)) := by
      have h1 : Integrable (fun u : ℝ => Real.exp (-u) * (u ^ (-α - η) + u ^ (-α + η)))
          (volume.restrict (Set.Ioi 0)) := by
        refine (hb1.add hb2).congr ?_
        filter_upwards with u
        rw [Pi.add_apply]
        ring
      have h2 : Integrable (fun u : ℝ => (1 + η) * B *
          (Real.exp (-u) * (u ^ (-α - η) + u ^ (-α + η)))) (volume.restrict (Set.Ioi 0)) :=
        h1.const_mul _
      have h3 : Integrable (fun u : ℝ => (1 + η) * B *
          (Real.exp (-u) * (u ^ (-α - η) + u ^ (-α + η))) + Real.exp (-u) * u ^ (-α))
          (volume.restrict (Set.Ioi 0)) := h2.add hb3
      refine h3.congr ?_
      filter_upwards with u
      ring
    have hexpint : Integrable (fun u : ℝ => Real.exp (-u)) (volume.restrict (Set.Ioi 0)) := by
      have h := integrableOn_exp_mul_Ioi (a := (-1:ℝ)) (by norm_num) (0:ℝ)
      have h2 : (fun x : ℝ => Real.exp (-1 * x)) = fun x => Real.exp (-x) := by
        ext x; rw [neg_one_mul]
      rw [h2] at h
      exact h
    have hintF : ∀ h : ℝ, Integrable (fun u : ℝ => Real.exp (-u) * F (u/h))
        (volume.restrict (Set.Ioi 0)) := by
      intro h
      refine hexpint.mono' ?_ ?_
      · exact ((Real.measurable_exp.comp measurable_id.neg).mul
          (hFmeas.comp (measurable_id.div_const h))).aestronglyMeasurable
      · filter_upwards with u
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hF0 (u/h))]
        nlinarith [hF1 (u/h), Real.exp_pos (-u)]
    -- ### Step 4: dominated convergence on `{u ≥ h X}`
    have hleX : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), h ≤ 1/X :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (show (0:ℝ) < 1 / X by positivity)) |>.mono (fun h hh => hh.le)
    -- ### Step 4a: the function `Φ` and its measurability
    set Φ : ℝ → ℝ → ℝ := fun h u => Real.exp (-u) *
      ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α)) with hΦdef
    have hΦeq : ∀ h u, Φ h u = Real.exp (-u) *
        ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α)) := by
      intro h u; rw [hΦdef]
    have hmeasΦ : ∀ h : ℝ, Measurable fun u : ℝ => Φ h u := by
      intro h
      have h1 : (fun u : ℝ => Φ h u) = fun u : ℝ => Real.exp (-u) *
          ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α)) := by
        ext u; exact hΦeq h u
      rw [h1]
      exact (Real.measurable_exp.comp measurable_id.neg).mul
        ((Measurable.mul measurable_const (hFmeas.comp (measurable_id.div_const h))).sub
          (by fun_prop))
    -- ### Step 4b: the three side conditions of dominated convergence
    have hside1 : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
        AEStronglyMeasurable (fun u : ℝ => (Set.Ici (h*X)).indicator (fun u => Real.exp (-u) *
          ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α))) u)
        (volume.restrict (Set.Ioi 0)) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact (hmeasind h).aestronglyMeasurable
    have hside2 : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
        ‖(Set.Ici (h*X)).indicator (fun u => Real.exp (-u) *
          ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α))) u‖
        ≤ Real.exp (-u) * ((1 + η) * B * (u ^ (-α - η) + u ^ (-α + η)) + u ^ (-α)) := by
      filter_upwards [self_mem_nhdsWithin, hleX] with h hh hle
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Set.indicator_apply]
      split_ifs with hmem
      · have hk := hkey h hh hle u hmem
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le
      · rw [norm_zero]
        have hu0 : (0:ℝ) < u := hu
        have h1 : 0 ≤ u ^ (-α - η) := le_of_lt (Real.rpow_pos_of_pos hu0 _)
        have h2 : 0 ≤ u ^ (-α + η) := le_of_lt (Real.rpow_pos_of_pos hu0 _)
        have h3 : 0 ≤ u ^ (-α) := le_of_lt (Real.rpow_pos_of_pos hu0 _)
        positivity
    have hside3 : ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
        Tendsto (fun h : ℝ => (Set.Ici (h*X)).indicator (fun u => Real.exp (-u) *
          ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α))) u)
        (𝓝[>] (0:ℝ)) (𝓝 (((fun _ => (0:ℝ)) : ℝ → ℝ) u)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      have hev : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), u ∈ Set.Ici (h*X) := by
        have h1 : ∀ᶠ h : ℝ in 𝓝 (0:ℝ), h * X < u := by
          have h2 : ∀ᶠ h : ℝ in 𝓝 (0:ℝ), h < u/X :=
            eventually_lt_nhds (by positivity)
          filter_upwards [h2] with h hh
          rw [lt_div_iff₀ hXpos] at hh
          linarith
        exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (h1.mono (fun h hh => le_of_lt hh))
      have hG : Tendsto (fun h : ℝ => (Real.Gamma (1 - α) / f (1/h)) * F (u/h))
          (𝓝[>] (0:ℝ)) (𝓝 (u ^ (-α))) := by
        have h1 := tendsto_ratio_F hαpos hu0 htail
        have h2 := tendsto_rv_ratio hu0 hrv
        have hprod := h1.mul h2
        rw [one_mul] at hprod
        have hcomp : Tendsto (fun h : ℝ => u/h) (𝓝[>] (0:ℝ)) atTop := by
          have := Tendsto.const_mul_atTop hu0 tendsto_inv_nhdsGT_zero
          simpa [div_eq_mul_inv] using this
        have hne : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), f (u/h) ≠ 0 :=
          (hcomp.eventually hposf_ev).mono (fun x hx => ne_of_gt hx)
        have hne2 : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), f (1/h) ≠ 0 := by
          have h1 : Tendsto (fun h : ℝ => 1/h) (𝓝[>] (0:ℝ)) atTop := by
            simpa [one_div] using tendsto_inv_nhdsGT_zero
          exact (h1.eventually hposf_ev).mono (fun x hx => ne_of_gt hx)
        refine hprod.congr' ?_
        filter_upwards [hne, hne2] with h hfne hfne2
        field_simp
      have hinner : Tendsto (fun h : ℝ => Real.exp (-u) *
          ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α)))
          (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have hsub : Tendsto (fun h : ℝ => (Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α))
            (𝓝[>] (0:ℝ)) (𝓝 (u ^ (-α) - u ^ (-α))) :=
          hG.sub (show Tendsto (fun _ : ℝ => u ^ (-α)) (𝓝[>] (0:ℝ)) (𝓝 (u ^ (-α))) from
            tendsto_const_nhds)
        rw [sub_self] at hsub
        have h2 := hsub.const_mul (Real.exp (-u))
        rw [mul_zero] at h2
        simpa [mul_sub] using h2
      refine hinner.congr' ?_
      filter_upwards [hev] with h hh
      rw [Set.indicator_of_mem hh]
    have hDCT : Tendsto (fun h : ℝ => ∫ u in Set.Ioi (0:ℝ),
        (Set.Ici (h*X)).indicator (fun u => Real.exp (-u) *
          ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α))) u)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hmain := tendsto_integral_filter_of_dominated_convergence
        (μ := volume.restrict (Set.Ioi 0)) (l := 𝓝[>] (0:ℝ)) (ι := ℝ)
        (F := fun h : ℝ => fun u : ℝ => (Set.Ici (h*X)).indicator (fun u => Real.exp (-u) *
          ((Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α))) u)
        (f := fun _ => (0:ℝ))
        (bound := fun u : ℝ => Real.exp (-u) *
          ((1 + η) * B * (u ^ (-α - η) + u ^ (-α + η)) + u ^ (-α)))
        hside1 hside2 hmaj hside3
      simpa using hmain
    -- ### Step 5: the small region `{u < h X}`
    have hpointAll : ∀ h : ℝ, 0 < h → 0 < f (1/h) → ∀ u : ℝ, 0 < u → ‖Φ h u‖
        ≤ Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h)) + Real.exp (-u) * u ^ (-α) := by
      intro h hh hposinv u hu0
      have hA : (0:ℝ) ≤ Real.Gamma (1 - α) / f (1/h) := le_of_lt (div_pos hΓpos hposinv)
      have key : |(Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α)|
          ≤ (Real.Gamma (1 - α) / f (1/h)) + u ^ (-α) := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (mul_nonneg hA (hF0 _)),
          abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos hu0 _))]
        have h5 : (Real.Gamma (1 - α) / f (1/h)) * F (u/h)
            ≤ (Real.Gamma (1 - α) / f (1/h)) := by
          calc (Real.Gamma (1 - α) / f (1/h)) * F (u/h)
              ≤ (Real.Gamma (1 - α) / f (1/h)) * 1 :=
                mul_le_mul_of_nonneg_left (hF1 (u/h)) hA
            _ = (Real.Gamma (1 - α) / f (1/h)) := mul_one _
        linarith
      have hnorm : ‖Φ h u‖ = Real.exp (-u) *
          |(Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α)| := by
        rw [hΦeq]
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [hnorm]
      calc Real.exp (-u) * |(Real.Gamma (1 - α) / f (1/h)) * F (u/h) - u ^ (-α)|
          ≤ Real.exp (-u) * ((Real.Gamma (1 - α) / f (1/h)) + u ^ (-α)) :=
            mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
        _ = Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h)) + Real.exp (-u) * u ^ (-α) := by
            ring
    -- integrability of `Φ h` on `(0,∞)`
    have hintΦ : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), Integrable (Φ h) (volume.restrict (Set.Ioi 0)) := by
      filter_upwards [self_mem_nhdsWithin, hleX] with h hh hle
      have hinvX : X ≤ 1/h := by
        rw [le_div_iff₀ hh]
        have h1 : h * X ≤ 1 := by
          have h2 := mul_le_mul_of_nonneg_right hle hXpos.le
          rwa [one_div, inv_mul_cancel₀ (ne_of_gt hXpos)] at h2
        linarith
      have hposinv : 0 < f (1/h) := (hX₂ (1/h) (le_trans hX₂X hinvX)).2
      have hmaj2 : Integrable (fun u : ℝ =>
          Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h)) + Real.exp (-u) * u ^ (-α))
          (volume.restrict (Set.Ioi 0)) :=
        (hexpint.mul_const _).add hb3
      refine Integrable.mono' (μ := volume.restrict (Set.Ioi 0)) hmaj2
        (hmeasΦ h).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hpointAll h hh hposinv u hu
    have hsmall : Tendsto (fun h : ℝ => ∫ u in Set.Ioo (0:ℝ) (h*X), Φ h u)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hbnd : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ),
          ‖∫ u in Set.Ioo (0:ℝ) (h*X), Φ h u‖
          ≤ Real.Gamma (1 - α) * X * (h / f (1/h)) + X ^ (1 - α) * h ^ (1 - α) / (1 - α) := by
        filter_upwards [self_mem_nhdsWithin, hleX] with h hh hle
        have hXh : (0:ℝ) < h * X := mul_pos hh hXpos
        have hinvX : X ≤ 1/h := by
          rw [le_div_iff₀ hh]
          have h1 : h * X ≤ 1 := by
            have h2 := mul_le_mul_of_nonneg_right hle hXpos.le
            rwa [one_div, inv_mul_cancel₀ (ne_of_gt hXpos)] at h2
          linarith
        have hposinv : 0 < f (1/h) := (hX₂ (1/h) (le_trans hX₂X hinvX)).2
        have hA : (0:ℝ) ≤ Real.Gamma (1 - α) / f (1/h) := le_of_lt (div_pos hΓpos hposinv)
        have hIntExp : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioo 0 (h*X)) :=
          IntegrableOn.mono_set hexpint (fun u hu => hu.1)
        have hIntRpow : IntegrableOn (fun u : ℝ => u ^ (-α)) (Set.Ioo 0 (h*X)) := by
          have h1 : IntervalIntegrable (fun u : ℝ => u ^ (-α)) volume 0 (h*X) :=
            intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < -α)
          exact IntegrableOn.mono_set h1.1 (fun u hu => ⟨hu.1, hu.2.le⟩)
        have hIntCmp : IntegrableOn (fun u : ℝ =>
            Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h)) + u ^ (-α)) (Set.Ioo 0 (h*X)) :=
          (hIntExp.mul_const _).add hIntRpow
        have hpoint : ∀ u ∈ Set.Ioo (0:ℝ) (h*X), ‖Φ h u‖
            ≤ Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h)) + u ^ (-α) := by
          intro u hu
          refine (hpointAll h hh hposinv u hu.1).trans ?_
          have h6 : Real.exp (-u) * u ^ (-α) ≤ u ^ (-α) := by
            calc Real.exp (-u) * u ^ (-α) ≤ 1 * u ^ (-α) := by
                  apply mul_le_mul_of_nonneg_right _
                    (le_of_lt (Real.rpow_pos_of_pos hu.1 _))
                  rw [← Real.exp_zero]
                  exact Real.exp_le_exp.2 (by linarith [hu.1])
              _ = u ^ (-α) := one_mul _
          rw [add_comm (Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h)))]
          rw [add_comm (Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h))) (u ^ (-α))]
          linarith [h6]
        have hIntNorm : IntegrableOn (fun u : ℝ => ‖Φ h u‖) (Set.Ioo 0 (h*X)) :=
          Integrable.mono' (μ := volume.restrict (Set.Ioo 0 (h*X))) hIntCmp
            (hmeasΦ h).norm.aestronglyMeasurable (by
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
              simpa using hpoint u hu)
        have hstep1 : ‖∫ u in Set.Ioo (0:ℝ) (h*X), Φ h u‖
            ≤ ∫ u in Set.Ioo (0:ℝ) (h*X), ‖Φ h u‖ := norm_integral_le_integral_norm _
        have hstep2 : ∫ u in Set.Ioo (0:ℝ) (h*X), ‖Φ h u‖
            ≤ ∫ u in Set.Ioo (0:ℝ) (h*X),
              (Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h)) + u ^ (-α)) :=
          setIntegral_mono_on hIntNorm hIntCmp measurableSet_Ioo hpoint
        have hstep3 : ∫ u in Set.Ioo (0:ℝ) (h*X),
              (Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h)) + u ^ (-α))
            = (Real.Gamma (1 - α) / f (1/h)) * (∫ u in Set.Ioo (0:ℝ) (h*X), Real.exp (-u))
              + ∫ u in Set.Ioo (0:ℝ) (h*X), u ^ (-α) := by
          rw [integral_add (hIntExp.mul_const _) hIntRpow, integral_mul_const]
          ring
        have hstep4 : ∫ u in Set.Ioo (0:ℝ) (h*X), Real.exp (-u) ≤ h*X := by
          have hc : ∫ u in Set.Ioo (0:ℝ) (h*X), (1:ℝ) = h*X := by
            rw [setIntegral_const, Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith),
              smul_eq_mul, mul_one, sub_zero]
          calc ∫ u in Set.Ioo (0:ℝ) (h*X), Real.exp (-u)
              ≤ ∫ u in Set.Ioo (0:ℝ) (h*X), (1:ℝ) := by
                refine setIntegral_mono_on hIntExp (integrableOn_const ?_) measurableSet_Ioo (fun u hu => ?_)
                · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
                · rw [← Real.exp_zero]
                  exact Real.exp_le_exp.2 (by linarith [hu.1])
            _ = h*X := hc
        have hstep5 : ∫ u in Set.Ioo (0:ℝ) (h*X), u ^ (-α) = (h*X) ^ (1 - α) / (1 - α) := by
          have h1 : ∫ u in (0:ℝ)..(h*X), u ^ (-α) = (h*X) ^ (1 - α) / (1 - α) := by
            rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < -α)),
              show -α + 1 = 1 - α from by ring,
              Real.zero_rpow (by linarith : (1:ℝ) - α ≠ 0), sub_zero]
          rw [← h1, intervalIntegral.integral_of_le hXh.le, ← integral_Ioc_eq_integral_Ioo]
        have hstep6 : (Real.Gamma (1 - α) / f (1/h)) * (h*X)
            = Real.Gamma (1 - α) * X * (h / f (1/h)) := by
          field_simp
        have hstep7 : (h*X) ^ (1 - α) / (1 - α) = X ^ (1 - α) * h ^ (1 - α) / (1 - α) := by
          rw [Real.mul_rpow hh.le hXpos.le]
          ring
        calc ‖∫ u in Set.Ioo (0:ℝ) (h*X), Φ h u‖
            ≤ ∫ u in Set.Ioo (0:ℝ) (h*X), ‖Φ h u‖ := hstep1
          _ ≤ ∫ u in Set.Ioo (0:ℝ) (h*X),
              (Real.exp (-u) * (Real.Gamma (1 - α) / f (1/h)) + u ^ (-α)) := hstep2
          _ = (Real.Gamma (1 - α) / f (1/h)) * (∫ u in Set.Ioo (0:ℝ) (h*X), Real.exp (-u))
              + ∫ u in Set.Ioo (0:ℝ) (h*X), u ^ (-α) := hstep3
          _ ≤ (Real.Gamma (1 - α) / f (1/h)) * (h*X) + (h*X) ^ (1 - α) / (1 - α) := by
              rw [hstep5]
              have hm := mul_le_mul_of_nonneg_left hstep4 hA
              linarith
          _ = Real.Gamma (1 - α) * X * (h / f (1/h)) + X ^ (1 - α) * h ^ (1 - α) / (1 - α) := by
              rw [hstep6, hstep7]
      have hlim1 : Tendsto (fun h : ℝ => Real.Gamma (1 - α) * X * (h / f (1/h))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have h0 : Tendsto (fun h : ℝ => h / f (1/h)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
          tendsto_div_of_regularlyVarying_neg hα1 hfmeas hrv
        have h1 := h0.const_mul (Real.Gamma (1 - α) * X)
        rwa [mul_zero] at h1
      have hlim2 : Tendsto (fun h : ℝ => X ^ (1 - α) * h ^ (1 - α) / (1 - α)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        have h1 : Tendsto (fun h : ℝ => h ^ (1 - α)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
          have hr : Tendsto (fun h : ℝ => h ^ (-(1 - α))) (𝓝[>] (0:ℝ)) atTop :=
            tendsto_rpow_neg_nhdsGT_zero (by linarith : -(1 - α) < 0)
          have hr2 : Tendsto (fun h : ℝ => (h ^ (-(1 - α)))⁻¹) (𝓝[>] (0:ℝ)) (𝓝 0) :=
            hr.inv_tendsto_atTop
          refine hr2.congr' ?_
          filter_upwards [self_mem_nhdsWithin] with h hh
          rw [Real.rpow_neg hh.le, inv_inv]
        have := (h1.const_mul (X ^ (1 - α))).div_const (1 - α)
        simpa [mul_zero, zero_div] using this
      exact squeeze_zero_norm' hbnd (by simpa using hlim1.add hlim2)
    -- ### Step 6: splitting the full integral
    have hzero : Tendsto (fun h : ℝ => ∫ u in Set.Ioi (0:ℝ), Φ h u)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hsplit : (fun h : ℝ => ∫ u in Set.Ioi (0:ℝ), Φ h u)
          =ᶠ[𝓝[>] (0:ℝ)] (fun h : ℝ => (∫ u in Set.Ioi (0:ℝ), (Set.Ici (h*X)).indicator (Φ h) u)
            + ∫ u in Set.Ioo (0:ℝ) (h*X), Φ h u) := by
        filter_upwards [self_mem_nhdsWithin, hintΦ, hside2] with h hh hΦ hbnd2
        have hInt1 : Integrable (fun u : ℝ => (Set.Ici (h*X)).indicator (Φ h) u)
            (volume.restrict (Set.Ioi 0)) :=
          hmaj.mono' (hmeasind h).aestronglyMeasurable hbnd2
        have hInt2 : Integrable (fun u : ℝ => (Set.Iio (h*X)).indicator (Φ h) u)
            (volume.restrict (Set.Ioi 0)) := hΦ.indicator measurableSet_Iio
        have hdec : ∀ u : ℝ, (Set.Ici (h*X)).indicator (Φ h) u + (Set.Iio (h*X)).indicator (Φ h) u
            = Φ h u := by
          intro u
          by_cases hu : u ∈ Set.Ici (h*X)
          · rw [Set.indicator_of_mem hu, Set.indicator_of_notMem, add_zero]
            simp only [Set.mem_Ici] at hu
            simp only [Set.mem_Iio]; linarith
          · rw [Set.indicator_of_notMem hu, Set.indicator_of_mem, zero_add]
            simp only [Set.mem_Ici] at hu
            simp only [Set.mem_Iio]; linarith
        have hseteq : ∫ u in Set.Ioi (0:ℝ), (Set.Iio (h*X)).indicator (Φ h) u
            = ∫ u in Set.Ioo (0:ℝ) (h*X), Φ h u := by
          rw [setIntegral_indicator measurableSet_Iio]
          rfl
        calc ∫ u in Set.Ioi (0:ℝ), Φ h u
            = ∫ u in Set.Ioi (0:ℝ),
                ((Set.Ici (h*X)).indicator (Φ h) u + (Set.Iio (h*X)).indicator (Φ h) u) := by
                refine integral_congr_ae ?_
                filter_upwards with u
                exact (hdec u).symm
          _ = (∫ u in Set.Ioi (0:ℝ), (Set.Ici (h*X)).indicator (Φ h) u)
              + ∫ u in Set.Ioi (0:ℝ), (Set.Iio (h*X)).indicator (Φ h) u := integral_add hInt1 hInt2
          _ = (∫ u in Set.Ioi (0:ℝ), (Set.Ici (h*X)).indicator (Φ h) u)
              + ∫ u in Set.Ioo (0:ℝ) (h*X), Φ h u := by
                rw [hseteq]
      have h1 : Tendsto (fun h : ℝ => (∫ u in Set.Ioi (0:ℝ), (Set.Ici (h*X)).indicator (Φ h) u)
          + ∫ u in Set.Ioo (0:ℝ) (h*X), Φ h u) (𝓝[>] (0:ℝ)) (𝓝 (0 + 0)) :=
        hDCT.add hsmall
      simpa using h1.congr' hsplit.symm
    -- ### Step 7: the base asymptotic
    have hbase : Tendsto (fun h : ℝ => (Real.Gamma (1 - α) / f (1/h)) *
        ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * F (u/h))
        (𝓝[>] (0:ℝ)) (𝓝 (Real.Gamma (1 - α))) := by
      have heq : (fun h : ℝ => (Real.Gamma (1 - α) / f (1/h)) *
            (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * F (u/h)))
          =ᶠ[𝓝[>] (0:ℝ)] (fun h : ℝ => Real.Gamma (1 - α) + ∫ u in Set.Ioi (0:ℝ), Φ h u) := by
        filter_upwards [self_mem_nhdsWithin, hintΦ] with h hh hΦ
        have h1 : (Real.Gamma (1 - α) / f (1/h)) * (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * F (u/h))
            = ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) *
              ((Real.Gamma (1 - α) / f (1/h)) * F (u/h)) := by
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards with u
          ring
        have h2 : ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) *
              ((Real.Gamma (1 - α) / f (1/h)) * F (u/h))
            = (∫ u in Set.Ioi (0:ℝ), Φ h u) + Real.Gamma (1 - α) := by
          have hsum : ∫ u in Set.Ioi (0:ℝ), (Φ h u + Real.exp (-u) * u ^ (-α))
              = (∫ u in Set.Ioi (0:ℝ), Φ h u) + Real.Gamma (1 - α) := by
            rw [integral_add hΦ hb3, Gamma_one_sub_eq_integral hα1]
          rw [← hsum]
          refine integral_congr_ae ?_
          filter_upwards with u
          simp only [hΦeq]
          ring
        rw [h1, h2]
        ring
      have h1 : Tendsto (fun h : ℝ => Real.Gamma (1 - α) + ∫ u in Set.Ioi (0:ℝ), Φ h u)
          (𝓝[>] (0:ℝ)) (𝓝 (Real.Gamma (1 - α) + 0)) :=
        tendsto_const_nhds.add hzero
      simpa using h1.congr' heq.symm
    -- ### Step 8: conclude
    have hone : Tendsto (fun h : ℝ => (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * F (u/h)) / f (1/h))
        (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have h2 := hbase.const_mul ((Real.Gamma (1 - α))⁻¹)
      rw [inv_mul_cancel₀ (ne_of_gt hΓpos)] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      by_cases hf : f (1/h) = 0
      · simp only [one_div] at hf ⊢
        simp [hf]
      · simp only [one_div] at hf ⊢
        field_simp
    exact hone
  · filter_upwards [hsub, self_mem_nhdsWithin] with h hh hpos
    rw [← hh]

/-! ### The probabilistic form (Theorem I.2.11, "if" direction) -/

/-- **Theorem I.2.11, Abelian direction, for probability measures on `[0,∞)`.**

Let `μ` be a probability measure on `ℝ` carried by `[0,∞)` (e.g. the law of a
nonnegative random variable) and let `f` be regularly varying of index `-α`,
`0 ≤ α < 1`.  If the tail of `μ` satisfies `μ((x,∞)) ~ f(x)/Γ(1-α)` then

  `E_μ[1 - e^{-h X}] ~ f(1/h)`   as `h ↓ 0`.

This is the Abelian half of Hutchcroft's Theorem I.2.11 (Feller XIII.5.2).
The full equivalence is in `Analysis/TauberianConverseComplete.lean`. -/
theorem laplace_tail_asymptotic_of_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hfmeas : Measurable f) (hrv : RegularlyVaryingAtTop f (-α))
    (htail : Tendsto (fun x => (μ (Set.Ioi x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1/h))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hanti : Antitone fun x : ℝ => μ (Set.Ioi x) :=
    fun a b hab => measure_mono (Set.Ioi_subset_Ioi hab)
  have hFmeas : Measurable fun x : ℝ => (μ (Set.Ioi x)).toReal :=
    hanti.measurable.ennreal_toReal
  have hF0 : ∀ x : ℝ, 0 ≤ (μ (Set.Ioi x)).toReal := fun x => ENNReal.toReal_nonneg
  have hF1 : ∀ x : ℝ, (μ (Set.Ioi x)).toReal ≤ 1 := by
    intro x
    have h1 : μ (Set.Ioi x) ≤ 1 := by
      have h2 : μ (Set.Ioi x) ≤ μ (Set.univ : Set ℝ) := measure_mono (Set.subset_univ _)
      have h3 : μ (Set.univ : Set ℝ) = 1 := IsProbabilityMeasure.measure_univ
      rw [h3] at h2
      exact h2
    calc (μ (Set.Ioi x)).toReal ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h1
      _ = 1 := by simp
  have hm := tendsto_laplace_of_tail_asymptotic (F := fun x : ℝ => (μ (Set.Ioi x)).toReal)
    hα0 hα1 hFmeas hF0 hF1 hfmeas hrv htail
  refine hm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [integral_one_sub_exp_eq_laplace_tail μ hμ hh]

/-! ### The uniqueness step of the Tauberian direction -/

/-- The partial integrals `L ↦ ∫_0^L e^{-u}u^{-α}du` tend to the full integral at `∞`. -/
theorem tendsto_partial_integral_atTop {α : ℝ} (hα : α < 1) :
    Tendsto (fun L : ℝ => ∫ u in Set.Ioo (0:ℝ) L, Real.exp (-u) * u ^ (-α))
      atTop (𝓝 (∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (-α))) := by
  have hint : Integrable (fun u : ℝ => Real.exp (-u) * u ^ (-α)) (volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_rpow (by linarith : (-1:ℝ) < -α)
  have hmeas : ∀ L : ℝ, AEStronglyMeasurable
      (fun u : ℝ => (Set.Ioo (0:ℝ) L).indicator (fun u => Real.exp (-u) * u ^ (-α)) u)
      (volume.restrict (Set.Ioi 0)) := by
    intro L
    refine Measurable.aestronglyMeasurable ?_
    exact ((Real.measurable_exp.comp measurable_id.neg).mul
      (by fun_prop : Measurable fun u : ℝ => u ^ (-α))).indicator measurableSet_Ioo
  have hcongr : (fun L : ℝ => ∫ u in Set.Ioo (0:ℝ) L, Real.exp (-u) * u ^ (-α))
      = fun L : ℝ => ∫ u in Set.Ioi (0:ℝ), (Set.Ioo (0:ℝ) L).indicator
          (fun u => Real.exp (-u) * u ^ (-α)) u := by
    ext L
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [show Set.Ioi (0:ℝ) ∩ Set.Ioo (0:ℝ) L = Set.Ioo (0:ℝ) L from by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
      tauto]
  rw [hcongr]
  have hb : ∀ᶠ L : ℝ in atTop, ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
      ‖(Set.Ioo (0:ℝ) L).indicator (fun u => Real.exp (-u) * u ^ (-α)) u‖
        ≤ Real.exp (-u) * u ^ (-α) := by
    filter_upwards with L
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, Set.indicator_apply]
    split_ifs with hmem
    · rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu.le _))]
    · rw [abs_zero]
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu.le _)
  have hlim : ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun L : ℝ => (Set.Ioo (0:ℝ) L).indicator (fun u => Real.exp (-u) * u ^ (-α)) u)
        atTop (𝓝 (Real.exp (-u) * u ^ (-α))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    have hev : ∀ᶠ L : ℝ in atTop, u ∈ Set.Ioo (0:ℝ) L :=
      eventually_atTop.2 ⟨u + 1, fun L hL => ⟨hu0, by linarith⟩⟩
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with L hL
    rw [Set.indicator_of_mem hL]
  simpa using tendsto_integral_filter_of_dominated_convergence (bound := fun u : ℝ =>
    Real.exp (-u) * u ^ (-α)) (Filter.Eventually.of_forall hmeas) hb hint hlim

/-- The partial integrals `L ↦ ∫_0^L e^{-u}u^{-α}du` tend to `0` at `0⁺`. -/
theorem tendsto_partial_integral_nhdsGT {α : ℝ} (hα : α < 1) :
    Tendsto (fun L : ℝ => ∫ u in Set.Ioo (0:ℝ) L, Real.exp (-u) * u ^ (-α))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hint : Integrable (fun u : ℝ => Real.exp (-u) * u ^ (-α)) (volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_rpow (by linarith : (-1:ℝ) < -α)
  have hmeas : ∀ L : ℝ, AEStronglyMeasurable
      (fun u : ℝ => (Set.Ioo (0:ℝ) L).indicator (fun u => Real.exp (-u) * u ^ (-α)) u)
      (volume.restrict (Set.Ioi 0)) := by
    intro L
    refine Measurable.aestronglyMeasurable ?_
    exact ((Real.measurable_exp.comp measurable_id.neg).mul
      (by fun_prop : Measurable fun u : ℝ => u ^ (-α))).indicator measurableSet_Ioo
  have hcongr : (fun L : ℝ => ∫ u in Set.Ioo (0:ℝ) L, Real.exp (-u) * u ^ (-α))
      = fun L : ℝ => ∫ u in Set.Ioi (0:ℝ), (Set.Ioo (0:ℝ) L).indicator
          (fun u => Real.exp (-u) * u ^ (-α)) u := by
    ext L
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [show Set.Ioi (0:ℝ) ∩ Set.Ioo (0:ℝ) L = Set.Ioo (0:ℝ) L from by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]
      tauto]
  rw [hcongr]
  have hb : ∀ᶠ L : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
      ‖(Set.Ioo (0:ℝ) L).indicator (fun u => Real.exp (-u) * u ^ (-α)) u‖
        ≤ Real.exp (-u) * u ^ (-α) := by
    filter_upwards with L
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, Set.indicator_apply]
    split_ifs with hmem
    · rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu.le _))]
    · rw [abs_zero]
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu.le _)
  have hlim : ∀ᵐ u ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun L : ℝ => (Set.Ioo (0:ℝ) L).indicator (fun u => Real.exp (-u) * u ^ (-α)) u)
        (𝓝[>] (0:ℝ)) (𝓝 ((fun _ => (0:ℝ)) u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    have hev : ∀ᶠ L : ℝ in 𝓝[>] (0:ℝ), u ∉ Set.Ioo (0:ℝ) L := by
      have h1 : ∀ᶠ L : ℝ in 𝓝[>] (0:ℝ), L < u :=
        (eventually_lt_nhds hu0).filter_mono nhdsWithin_le_nhds
      filter_upwards [h1] with L hL
      simp only [Set.mem_Ioo]
      rintro ⟨-, h2⟩
      linarith
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with L hL
    rw [Set.indicator_of_notMem hL]
  simpa using tendsto_integral_filter_of_dominated_convergence (bound := fun u : ℝ =>
    Real.exp (-u) * u ^ (-α)) (Filter.Eventually.of_forall hmeas) hb hint hlim

/-- **Uniqueness step of the Karamata Tauberian theorem.**

Let `α ∈ [0,1)`, let `φ : ℝ → ℝ` be nonincreasing, nonnegative and bounded, and
suppose that *all* the kernel averages

  `δ ↦ ∫_0^∞ e^{-u} u^{-α} φ(δ + log u) du`

equal the constant `Γ(1-α)·c`.  Then `φ ≡ c`.

In the log scale the hypothesis of Theorem I.2.11 becomes exactly the statement
that the convolution of `ψ = Ψ/ω` with the probability density `k(v) = e^{v-e^v}`
is constant, and this lemma says that a *nonincreasing* `ψ` with constant kernel
averages is constant.  (Monotonicity cannot be dropped: the averages are a
one-sided smoothing.)

Proof: as `δ → -∞` the mass of `u ↦ e^{-u}u^{-α}` concentrates at `u → 0`, i.e.
at `s = δ + log u ≤ v₀`, where `φ ≥ φ(v₀)`; hence `Γc ≥ φ(v₀)Γ`.  As `δ → +∞`
the mass concentrates at `s = δ + log u ≥ v₀`, where `φ ≤ φ(v₀)`; hence
`Γc ≤ φ(v₀)Γ`.  Therefore `φ(v₀) = c`. -/
theorem unique_of_kernel_averages {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {φ : ℝ → ℝ} (hmono : Antitone φ) (h0 : ∀ v, 0 ≤ φ v) (hB : ∃ B, ∀ v, φ v ≤ B)
    (havg : ∀ δ : ℝ, ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u)
      = Real.Gamma (1 - α) * c) :
    ∀ v, φ v = c := by
  obtain ⟨B, hB⟩ := hB
  have hα1' : (0:ℝ) < 1 - α := by linarith
  have hΓpos : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos hα1'
  have hΓeq : Real.Gamma (1 - α) = ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (-α) :=
    Gamma_one_sub_eq_integral hα1
  have hgint : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ (-α)) (Set.Ioi 0) :=
    integrableOn_exp_mul_rpow (by linarith : (-1:ℝ) < -α)
  have hg0 : ∀ u : ℝ, 0 < u → 0 ≤ Real.exp (-u) * u ^ (-α) := fun u hu =>
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu.le _)
  have hφmeas : Measurable φ := hmono.measurable
  have hmeasf : ∀ δ : ℝ, AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u))
      (volume.restrict (Set.Ioi 0)) := by
    intro δ
    refine Measurable.aestronglyMeasurable ?_
    exact ((Real.measurable_exp.comp measurable_id.neg).mul
      (by fun_prop : Measurable fun u : ℝ => u ^ (-α))).mul
      (hφmeas.comp (measurable_const.add Real.measurable_log))
  have hint : ∀ δ : ℝ, IntegrableOn
      (fun u : ℝ => Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u)) (Set.Ioi 0) := by
    intro δ
    refine Integrable.mono' (μ := volume.restrict (Set.Ioi 0)) (hgint.const_mul B)
      (hmeasf δ) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 u hu), abs_of_nonneg (h0 _),
      mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB _) (hg0 u hu)
  -- integrability on the pieces used below
  have hintOn : ∀ δ : ℝ, ∀ s : Set ℝ, s ⊆ Set.Ioi (0:ℝ) →
      IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u)) s := by
    intro δ s hs
    exact (hint δ).mono_set hs
  have hgOn : ∀ s : Set ℝ, s ⊆ Set.Ioi (0:ℝ) →
      IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ (-α)) s := by
    intro s hs
    exact hgint.mono_set hs
  -- ## `φ v₀ ≤ c`, using `δ → -∞`
  have hupper : ∀ v₀ : ℝ, φ v₀ ≤ c := by
    intro v₀
    have hexp : Tendsto (fun δ : ℝ => Real.exp (v₀ - δ)) atBot atTop := by
      refine Real.tendsto_exp_atTop.comp ?_
      rw [tendsto_atTop]
      intro a
      rw [eventually_atBot]
      exact ⟨v₀ - a, fun δ hδ => by linarith⟩
    have hlim : Tendsto (fun δ : ℝ => φ v₀ *
        ∫ u in Set.Ioo (0:ℝ) (Real.exp (v₀ - δ)), Real.exp (-u) * u ^ (-α))
        atBot (𝓝 (φ v₀ * Real.Gamma (1 - α))) := by
      have h1 := (tendsto_partial_integral_atTop (α := α) hα1).comp hexp
      rw [← hΓeq] at h1
      exact h1.const_mul _
    have hmono2 : ∀ δ : ℝ, φ v₀ * (∫ u in Set.Ioo (0:ℝ) (Real.exp (v₀ - δ)),
        Real.exp (-u) * u ^ (-α)) ≤ Real.Gamma (1 - α) * c := by
      intro δ
      have hLpos : (0:ℝ) < Real.exp (v₀ - δ) := Real.exp_pos _
      have hstep1 : φ v₀ * (∫ u in Set.Ioo (0:ℝ) (Real.exp (v₀ - δ)), Real.exp (-u) * u ^ (-α))
          ≤ ∫ u in Set.Ioo (0:ℝ) (Real.exp (v₀ - δ)),
              Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u) := by
        rw [mul_comm (φ v₀), ← integral_mul_const]
        refine setIntegral_mono_on
          ((hgOn (Set.Ioo 0 (Real.exp (v₀ - δ))) (fun u hu => hu.1)).mul_const (φ v₀))
          (hintOn δ (Set.Ioo 0 (Real.exp (v₀ - δ))) (fun u hu => hu.1)) measurableSet_Ioo ?_
        · intro u hu
          rw [Set.mem_Ioo] at hu
          have hlog : Real.log u < v₀ - δ := (Real.log_lt_iff_lt_exp hu.1).2 hu.2
          have hlt : δ + Real.log u ≤ v₀ := by linarith
          have h1 : φ v₀ ≤ φ (δ + Real.log u) := hmono hlt
          exact mul_le_mul_of_nonneg_left h1 (hg0 u hu.1)
      have hstep2 : ∫ u in Set.Ioo (0:ℝ) (Real.exp (v₀ - δ)),
            Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u)
          ≤ ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u) := by
        refine setIntegral_mono_set (hint δ) ?_ ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact mul_nonneg (hg0 u hu) (h0 _)
        · filter_upwards with u hu
          exact hu.1
      rw [← havg δ]
      exact le_trans hstep1 hstep2
    have hle : φ v₀ * Real.Gamma (1 - α) ≤ Real.Gamma (1 - α) * c :=
      le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Filter.Eventually.of_forall hmono2)
    nlinarith [hΓpos]
  -- ## `c ≤ φ v₀`, using `δ → +∞`
  have hlower : ∀ v₀ : ℝ, c ≤ φ v₀ := by
    intro v₀
    have hexp : Tendsto (fun δ : ℝ => Real.exp (v₀ - δ)) atTop (𝓝[>] (0:ℝ)) := by
      have h1 : Tendsto (fun δ : ℝ => v₀ - δ) atTop atBot := by
        rw [tendsto_atBot]
        intro a
        rw [eventually_atTop]
        exact ⟨v₀ - a, fun δ hδ => by linarith⟩
      have h2 := Real.tendsto_exp_atBot.comp h1
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h2, Filter.Eventually.of_forall (fun δ => Real.exp_pos _)⟩
    have hlim : Tendsto (fun δ : ℝ => B * (∫ u in Set.Ioo (0:ℝ) (Real.exp (v₀ - δ)),
        Real.exp (-u) * u ^ (-α))) atTop (𝓝 0) := by
      have h1 := (tendsto_partial_integral_nhdsGT (α := α) hα1).comp hexp
      simpa using h1.const_mul B
    have hbound : ∀ δ : ℝ, Real.Gamma (1 - α) * c ≤ B * (∫ u in Set.Ioo (0:ℝ)
        (Real.exp (v₀ - δ)), Real.exp (-u) * u ^ (-α)) + φ v₀ * Real.Gamma (1 - α) := by
      intro δ
      have hLpos : (0:ℝ) < Real.exp (v₀ - δ) := Real.exp_pos _
      -- split `(0,∞) = (0,L) ∪ [L,∞)`
      have hsplit : ∫ u in Set.Ioi (0:ℝ), Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u)
          = (∫ u in Set.Ioo (0:ℝ) (Real.exp (v₀ - δ)),
                Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u))
            + ∫ u in Set.Ici (Real.exp (v₀ - δ)),
                Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u) := by
        have hset : Set.Ioi (0:ℝ) = Set.Ioo 0 (Real.exp (v₀ - δ)) ∪ Set.Ici (Real.exp (v₀ - δ)) := by
          ext u
          simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
          constructor
          · intro h
            by_cases h2 : u < Real.exp (v₀ - δ)
            · exact Or.inl ⟨h, h2⟩
            · exact Or.inr (by linarith)
          · rintro (⟨h1, -⟩ | h2)
            · exact h1
            · linarith
        rw [hset]
        refine setIntegral_union ?_ measurableSet_Ici
          (hintOn δ (Set.Ioo 0 (Real.exp (v₀ - δ))) (fun u hu => hu.1))
          (hintOn δ (Set.Ici (Real.exp (v₀ - δ))) (fun u hu => lt_of_lt_of_le hLpos hu))
        rw [Set.disjoint_left]
        intro u hu1 hu2
        rw [Set.mem_Ioo] at hu1
        rw [Set.mem_Ici] at hu2
        linarith
      rw [← havg δ, hsplit]
      have hpiece1 : ∫ u in Set.Ioo (0:ℝ) (Real.exp (v₀ - δ)),
            Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u)
          ≤ B * (∫ u in Set.Ioo (0:ℝ) (Real.exp (v₀ - δ)), Real.exp (-u) * u ^ (-α)) := by
        rw [mul_comm B, ← integral_mul_const]
        refine setIntegral_mono_on
          (hintOn δ (Set.Ioo 0 (Real.exp (v₀ - δ))) (fun u hu => hu.1))
          ((hgOn (Set.Ioo 0 (Real.exp (v₀ - δ))) (fun u hu => hu.1)).mul_const B) measurableSet_Ioo ?_
        · intro u hu
          rw [Set.mem_Ioo] at hu
          exact mul_le_mul_of_nonneg_left (hB _) (hg0 u hu.1)
      have hpiece2 : ∫ u in Set.Ici (Real.exp (v₀ - δ)),
            Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u)
          ≤ φ v₀ * Real.Gamma (1 - α) := by
        have h1 : ∫ u in Set.Ici (Real.exp (v₀ - δ)),
              Real.exp (-u) * u ^ (-α) * φ (δ + Real.log u)
            ≤ φ v₀ * (∫ u in Set.Ici (Real.exp (v₀ - δ)), Real.exp (-u) * u ^ (-α)) := by
          rw [mul_comm (φ v₀), ← integral_mul_const]
          refine setIntegral_mono_on
            (hintOn δ (Set.Ici (Real.exp (v₀ - δ))) (fun u hu => lt_of_lt_of_le hLpos hu))
            ((hgOn (Set.Ici (Real.exp (v₀ - δ))) (fun u hu => lt_of_lt_of_le hLpos hu)).mul_const (φ v₀))
            measurableSet_Ici ?_
          · intro u hu
            rw [Set.mem_Ici] at hu
            have hlog : v₀ - δ ≤ Real.log u := (Real.le_log_iff_exp_le (lt_of_lt_of_le hLpos hu)).2 hu
            have h1 : φ (δ + Real.log u) ≤ φ v₀ := hmono (by linarith)
            exact mul_le_mul_of_nonneg_left h1 (hg0 u (lt_of_lt_of_le hLpos hu))
        have h2 : φ v₀ * (∫ u in Set.Ici (Real.exp (v₀ - δ)), Real.exp (-u) * u ^ (-α))
            ≤ φ v₀ * Real.Gamma (1 - α) := by
          refine mul_le_mul_of_nonneg_left ?_ (h0 v₀)
          rw [hΓeq]
          refine setIntegral_mono_set hgint ?_ ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            exact hg0 u hu
          · filter_upwards with u hu
            exact lt_of_lt_of_le hLpos hu
        linarith
      linarith [hpiece1, hpiece2]
    have hle : Real.Gamma (1 - α) * c ≤ φ v₀ * Real.Gamma (1 - α) :=
      le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa using hlim.add tendsto_const_nhds)
        (Filter.Eventually.of_forall hbound)
    nlinarith [hΓpos]
  intro v
  exact le_antisymm (hupper v) (hlower v)
