/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Potter's bounds and the uniform convergence theorem for the class of regularly
varying functions that arise in T. Hutchcroft, *Critical long-range percolation
I: High effective dimension*, arXiv:2508.18807v1, Section I.2.2.

The paper's Lemma I.2.10 (Karamata's integral theorem, `lemma_I_2_10` in
`CriticalPercLib.CriticalLRP/Analysis/KaramataMain.lean`) is currently proved
from the hypothesis `HasPotterBounds f α`, the classical Potter bounds
(Bingham–Goldie–Teugels, Theorem 1.5.6), which in the literature are derived
from the uniform convergence theorem (BGT Theorem 1.2.1) plus the Karamata
representation theorem.  In this file we discharge `HasPotterBounds` for the
concrete class of functions to which the paper applies Lemma I.2.10: solutions
of the linear ODE

  `f' = a (1 - h) f / t`   on `(0,∞)`   with   `h` measurable and `h → 0`

(the class of Lemma I.2.12 of the paper, which is exactly the class the paper
produces by differentiating its volume functions; see the proof of Lemma
I.4.21, where Lemma I.2.10 is applied to such an exponential factor times `h`).

Main results:

* `hasPotterBounds_of_ode` : Potter's bounds for this class, from the explicit
  ODE representation `ode_solution_mul` already proved in
  `Analysis/RegularVariation.lean`.  No other input is needed: the oscillating
  factor `exp (-a ∫_y^x h(s) ds/s)` is controlled by `sup_{s≥X} |h s|`.
* `tendsto_uniformly_ratio_of_ode` : the uniform convergence theorem (BGT
  Theorem 1.2.1) for this class: `f (l x) / f x → l ^ a` uniformly in
  `l ∈ [u,v] ⊂ (0,∞)`.
* `lemma_I_2_10_of_differentiable` : Karamata's integral theorem (paper Lemma
  I.2.10, the `α > -1` half) **with no Potter hypothesis**, for the class of
  Lemma I.2.12.

The general statement "measurable, regularly varying `f` ⟹ Potter's bounds"
for an arbitrary `f` is *not* proved here; see the note at the end of the file
for exactly what remains (the general BGT Theorem 1.2.1).
-/
module

public import PercLib.CriticalLRP.Analysis.KaramataMain

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

/-! ### Bounds for the oscillating exponential factor -/

/-- If `|I| ≤ δ L` with `δ, L ≥ 0` then `exp (-(a I)) ≤ exp (a δ L)`. -/
theorem exp_neg_mul_le {a I δ L : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hI : |I| ≤ δ * L) :
    Real.exp (-(a * I)) ≤ Real.exp (a * δ * L) := by
  apply Real.exp_le_exp.2
  have h1 := (abs_le.1 hI).1
  have hδL : 0 ≤ δ * L := mul_nonneg hδ hL
  nlinarith [h1, ha, hδL]

/-- If `|I| ≤ δ L` with `δ, L ≥ 0` then `exp (-(a δ L)) ≤ exp (-(a I))`. -/
theorem exp_le_exp_neg_mul {a I δ L : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hI : |I| ≤ δ * L) :
    Real.exp (-(a * δ * L)) ≤ Real.exp (-(a * I)) := by
  apply Real.exp_le_exp.2
  have h1 := (abs_le.1 hI).2
  have hδL : 0 ≤ δ * L := mul_nonneg hδ hL
  nlinarith [h1, ha, hδL]

/-- `exp (a δ log (x/y)) = (x/y) ^ (a δ)` for `x, y > 0`. -/
theorem exp_mul_log_eq_rpow {a δ x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (a * δ * Real.log (x / y)) = (x / y) ^ (a * δ) := by
  rw [Real.rpow_def_of_pos (div_pos hx hy), mul_comm]

/-- `exp (-(a δ log (x/y))) = (x/y) ^ (-(a δ))` for `x, y > 0`. -/
theorem exp_neg_mul_log_eq_rpow {a δ x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (-(a * δ * Real.log (x / y))) = (x / y) ^ (-(a * δ)) := by
  rw [Real.rpow_def_of_pos (div_pos hx hy)]
  congr 1
  ring

/-! ### Potter's bounds for solutions of `f' = a (1 - h) f / t` -/

/-- **Potter's bounds (BGT Theorem 1.5.6) for the ODE class.**  If `f` is a
positive solution of `f' = a (1 - h) f / t` on `(0,∞)` with `a > 0` and `h`
measurable, `h → 0`, then for every `ε > 0` and all `x ≥ y ≥ X = X(ε)`,

  `(1 - ε) (x/y)^{a-ε} f y ≤ f x ≤ (1 + ε) (x/y)^{a+ε} f y`.

This is `HasPotterBounds f a`, the hypothesis consumed by `lemma_I_2_10`. -/
theorem hasPotterBounds_of_ode {f f' h : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hode : ∀ t, 0 < t → f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (h0 : Tendsto h atTop (𝓝 0)) :
    HasPotterBounds f a := by
  intro ε hε
  set δ : ℝ := ε / (2 * a) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ t : ℝ, X₀ ≤ t → |h t| ≤ δ := by
    obtain ⟨X₀, hX₀⟩ := Metric.tendsto_atTop.1 h0 δ hδpos
    exact ⟨X₀, fun t ht => by
      have h := hX₀ t ht
      rw [Real.dist_eq, sub_zero, abs_lt] at h
      exact abs_le.2 ⟨le_of_lt h.1, le_of_lt h.2⟩⟩
  set X : ℝ := max X₀ 1 with hXdef
  have hX1 : 1 ≤ X := le_max_right _ _
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hXX₀ : X₀ ≤ X := le_max_left _ _
  refine ⟨X, hX1, fun x y hy hyx => ?_⟩
  have hypos : 0 < y := lt_of_lt_of_le hX0 hy
  have hxpos : 0 < x := lt_of_lt_of_le hypos hyx
  -- the ODE representation between `y` and `x`
  have hrep : f x = f y * (x / y) ^ a * Real.exp (-(a * ∫ s in y..x, h s / s)) :=
    ode_solution_mul ha hX0 (fun t ht => hderiv t (lt_of_lt_of_le hX0 ht))
      (fun t ht => hpos t (lt_of_lt_of_le hX0 ht))
      (fun t ht => hode t (lt_of_lt_of_le hX0 ht)) hmeas
      (fun t ht => hX₀ t (le_trans hXX₀ ht)) hy hyx
  -- the oscillation bound
  have hI : |∫ s in y..x, h s / s| ≤ δ * Real.log (x / y) :=
    abs_intervalIntegral_div_le hmeas hypos hyx
      (fun s hs => hX₀ s (le_trans hXX₀ (le_trans hy hs)))
  have hL : 0 ≤ Real.log (x / y) := Real.log_nonneg (by rw [le_div_iff₀ hypos]; linarith)
  have hδL : 0 ≤ δ * Real.log (x / y) := mul_nonneg hδpos.le hL
  have hfy : 0 < f y := hpos y (lt_of_lt_of_le hX0 hy)
  have hfx : 0 < f x := hpos x (lt_of_lt_of_le hX0 (le_trans hy hyx))
  have habsy : |f y| = f y := abs_of_pos hfy
  have habsx : |f x| = f x := abs_of_pos hfx
  have hratio1 : 1 ≤ x / y := by rw [le_div_iff₀ hypos]; linarith
  have haδ : a * δ = ε / 2 := by rw [hδdef]; field_simp
  constructor
  · -- lower bound
    have hlow : Real.exp (-(a * δ * Real.log (x / y))) ≤
        Real.exp (-(a * ∫ s in y..x, h s / s)) :=
      exp_le_exp_neg_mul ha hδpos.le hL hI
    have hrpow : Real.exp (-(a * δ * Real.log (x / y))) = (x / y) ^ (-(a * δ)) :=
      exp_neg_mul_log_eq_rpow hxpos hypos
    have h1 : f y * (x / y) ^ a * (x / y) ^ (-(a * δ)) ≤
        f y * (x / y) ^ a * Real.exp (-(a * ∫ s in y..x, h s / s)) := by
      have h2 : 0 ≤ f y * (x / y) ^ a := by
        have := Real.rpow_nonneg (le_of_lt (div_pos hxpos hypos)) a
        positivity
      calc f y * (x / y) ^ a * (x / y) ^ (-(a * δ))
          = f y * (x / y) ^ a * Real.exp (-(a * δ * Real.log (x / y))) := by rw [hrpow]
        _ ≤ f y * (x / y) ^ a * Real.exp (-(a * ∫ s in y..x, h s / s)) := by
            exact mul_le_mul_of_nonneg_left hlow h2
    have h3 : f y * (x / y) ^ a * (x / y) ^ (-(a * δ))
        = f y * (x / y) ^ (a - ε / 2) := by
      rw [mul_assoc, ← Real.rpow_add (by positivity), show a + -(a * δ) = a - ε / 2 by
        rw [haδ]; ring]
    have h4 : (x / y) ^ (a - ε) ≤ (x / y) ^ (a - ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hratio1 (by linarith)
    have h5 : 0 < f y := hfy
    rw [habsy, habsx]
    calc (1 - ε) * (x / y) ^ (a - ε) * f y ≤ 1 * (x / y) ^ (a - ε) * f y := by
          have h6 : 0 ≤ (x / y) ^ (a - ε) * f y := by
            have := Real.rpow_nonneg (le_of_lt (div_pos hxpos hypos)) (a - ε)
            positivity
          nlinarith [h6]
      _ = f y * (x / y) ^ (a - ε) := by ring
      _ ≤ f y * (x / y) ^ (a - ε / 2) := mul_le_mul_of_nonneg_left h4 hfy.le
      _ = f y * (x / y) ^ a * (x / y) ^ (-(a * δ)) := by rw [← h3]
      _ ≤ f y * (x / y) ^ a * Real.exp (-(a * ∫ s in y..x, h s / s)) := h1
      _ = f x := hrep.symm
  · -- upper bound
    have hup : Real.exp (-(a * ∫ s in y..x, h s / s)) ≤
        Real.exp (a * δ * Real.log (x / y)) :=
      exp_neg_mul_le ha hδpos.le hL hI
    have hrpow : Real.exp (a * δ * Real.log (x / y)) = (x / y) ^ (a * δ) :=
      exp_mul_log_eq_rpow hxpos hypos
    have h1 : f y * (x / y) ^ a * Real.exp (-(a * ∫ s in y..x, h s / s)) ≤
        f y * (x / y) ^ a * (x / y) ^ (a * δ) := by
      rw [hrpow] at hup
      have h2 : 0 ≤ f y * (x / y) ^ a := by
        have := Real.rpow_nonneg (le_of_lt (div_pos hxpos hypos)) a
        positivity
      exact mul_le_mul_of_nonneg_left hup h2
    have h3 : f y * (x / y) ^ a * (x / y) ^ (a * δ) = f y * (x / y) ^ (a + ε / 2) := by
      rw [mul_assoc, ← Real.rpow_add (by positivity), haδ]
    have h4 : (x / y) ^ (a + ε / 2) ≤ (x / y) ^ (a + ε) :=
      Real.rpow_le_rpow_of_exponent_le hratio1 (by linarith)
    rw [habsy, habsx]
    calc f x = f y * (x / y) ^ a * Real.exp (-(a * ∫ s in y..x, h s / s)) := hrep
      _ ≤ f y * (x / y) ^ a * (x / y) ^ (a * δ) := h1
      _ = f y * (x / y) ^ (a + ε / 2) := h3
      _ ≤ f y * (x / y) ^ (a + ε) := mul_le_mul_of_nonneg_left h4 hfy.le
      _ ≤ (1 + ε) * (x / y) ^ (a + ε) * f y := by
          have h6 : 0 ≤ (x / y) ^ (a + ε) * f y := by
            have := Real.rpow_nonneg (le_of_lt (div_pos hxpos hypos)) (a + ε)
            positivity
          nlinarith [h6]



/-! ### Karamata's integral theorem for the ODE class (paper Lemma I.2.10) -/

/-- **Karamata's integral theorem (paper Lemma I.2.10, `α > -1` case) for solutions
of `f' = a (1 - h) f / t`.**  If `a > 0`, `f : (0,∞) → (0,∞)` is differentiable
with `f' = a (1 - h) f / t` and `h` is measurable with `h → 0`, then

  `∫_1^r f(s) ds ∼ r f(r) / (a + 1)`   as `r → ∞`.

Compared with `lemma_I_2_10`, the hypotheses `Measurable f`,
`LocallyIntegrableOn f (Ioi 0)` and, crucially, `HasPotterBounds f a` are all
*derived* here, the latter from `hasPotterBounds_of_ode`. -/
theorem lemma_I_2_10_of_differentiable {f f' h : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hode : ∀ t, 0 < t → f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (h0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun r => (∫ s in 1..r, f s) / (r * f r)) atTop (𝓝 (1 / (a + 1))) := by
  classical
  -- extend `f` by `0` off `(0,∞)` so that it is globally measurable
  set F : ℝ → ℝ := (Ioi (0 : ℝ)).piecewise f 0 with hFdef
  have hFmem : ∀ t : ℝ, 0 < t → F t = f t := by
    intro t ht
    simp only [hFdef, Set.piecewise_eq_of_mem _ _ _ (mem_Ioi.2 ht)]
  have hcont : ContinuousOn f (Ioi (0 : ℝ)) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hFmeas : Measurable F :=
    hcont.measurable_piecewise continuousOn_const measurableSet_Ioi
  have hFcont : ContinuousOn F (Ioi (0 : ℝ)) := by
    refine hcont.congr ?_
    intro t ht
    exact hFmem t ht
  have hFloc : LocallyIntegrableOn F (Ioi (0 : ℝ)) volume :=
    hFcont.locallyIntegrableOn measurableSet_Ioi
  -- the ODE hypotheses for `F`
  have hFderiv : ∀ t, 0 < t → HasDerivAt F (f' t) t := by
    intro t ht
    refine (hderiv t ht).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact hFmem s hs
  have hFpos : ∀ t, 0 < t → 0 < F t := fun t ht => by rw [hFmem t ht]; exact hpos t ht
  have hFode : ∀ t, 0 < t → f' t = a * (1 - h t) * F t / t := by
    intro t ht
    rw [hFmem t ht]
    exact hode t ht
  have hFpot : HasPotterBounds F a :=
    hasPotterBounds_of_ode ha hFderiv hFpos hFode hmeas h0
  have hFrv : RegularlyVaryingAtTop F a := by
    have hrv : RegularlyVaryingAtTop f a :=
      lemma_I_2_12_rv ha one_pos (fun t ht => hderiv t (lt_of_lt_of_le one_pos ht))
        (fun t ht => hpos t (lt_of_lt_of_le one_pos ht))
        (fun t ht => hode t (lt_of_lt_of_le one_pos ht)) hmeas h0
    constructor
    · filter_upwards [hrv.1, eventually_ge_atTop (1 : ℝ)] with x hx hx1
      rwa [hFmem x (lt_of_lt_of_le one_pos hx1)]
    · intro l hl
      refine (hrv.2 l hl).congr' ?_
      filter_upwards [eventually_ge_atTop (max (1:ℝ) (1 / l))] with x hx
      have hx1 : (1:ℝ) ≤ x := le_trans (le_max_left _ _) hx
      have hxl : (1:ℝ) ≤ l * x := by
        have h2 : 1 / l ≤ x := le_trans (le_max_right _ _) hx
        rw [div_le_iff₀ hl] at h2
        linarith
      rw [hFmem x (lt_of_lt_of_le one_pos hx1), hFmem (l * x) (lt_of_lt_of_le one_pos hxl)]
  have hFposf : ∀ᶠ x in atTop, 0 < F x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [hFmem x (lt_of_lt_of_le one_pos hx)]
    exact hpos x (lt_of_lt_of_le one_pos hx)
  have hmain := lemma_I_2_10 (by linarith : -1 < a) hFmeas hFloc hFposf hFrv hFpot
  -- transfer back from `F` to `f` on `[1,∞)`
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hInt : ∫ s in 1..r, F s = ∫ s in 1..r, f s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr] at hs
    exact hFmem s (lt_of_lt_of_le one_pos hs.1)
  rw [hInt, hFmem r hr0]



/-! ### The uniform convergence theorem for the ODE class -/

/-- An interval integral of `h s / s` against `|log l|`: if `|h| ≤ δ` on `[X,∞)` and
`x, l x ≥ X > 0`, then `|∫_{l x}^{x} …|`-type oscillates by at most `δ |log l|`. -/
theorem abs_intervalIntegral_div_le_mul_abs_log {h : ℝ → ℝ} {δ X x l : ℝ}
    (hmeas : Measurable h) (hX : 0 < X) (hx : X ≤ x) (hl : 0 < l) (hlx : X ≤ l * x)
    (hbdd : ∀ t, X ≤ t → |h t| ≤ δ) :
    |∫ s in x..l * x, h s / s| ≤ δ * |Real.log l| := by
  have hxpos : 0 < x := lt_of_lt_of_le hX hx
  have hlxpos : 0 < l * x := lt_of_lt_of_le hX hlx
  rcases le_or_gt 1 l with h1 | h1
  · have hle : x ≤ l * x := by nlinarith
    have hb := abs_intervalIntegral_div_le hmeas hxpos hle
      (fun s hs => hbdd s (le_trans hx hs))
    have hlog : Real.log (l * x / x) = Real.log l := by
      rw [mul_div_cancel_right₀ l (ne_of_gt hxpos)]
    rw [hlog] at hb
    calc |∫ s in x..l * x, h s / s| ≤ δ * Real.log l := hb
      _ = δ * |Real.log l| := by rw [abs_of_nonneg (Real.log_nonneg h1)]
  · have hle : l * x ≤ x := by nlinarith
    have hb := abs_intervalIntegral_div_le hmeas hlxpos hle
      (fun s hs => hbdd s (le_trans hlx hs))
    have hlog : Real.log (x / (l * x)) = -Real.log l := by
      rw [show x / (l * x) = l⁻¹ by field_simp, Real.log_inv]
    rw [hlog] at hb
    have hsymm : ∫ s in x..l * x, h s / s = -(∫ s in l * x..x, h s / s) :=
      intervalIntegral.integral_symm (l * x) x
    rw [hsymm, abs_neg]
    calc |∫ s in l * x..x, h s / s| ≤ δ * -Real.log l := hb
      _ = δ * |Real.log l| := by rw [abs_of_neg (Real.log_neg hl h1)]



/-! ### The uniform convergence theorem for the ODE class -/

/-- **Ratio identity.**  For a positive solution of `f' = a (1 - h) f / t` and any `l > 0`,

  `f (l x) / f x = l ^ a * exp (-(a ∫_x^{l x} h(s) ds/s))`,

uniformly in the sign of `log l` (the interval integral is oriented). -/
theorem ratio_eq_of_ode {f f' h : ℝ → ℝ} {a r₀ C x l : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hode : ∀ t, r₀ ≤ t → f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (hx : r₀ ≤ x) (hl : 0 < l) (hlx : r₀ ≤ l * x) :
    f (l * x) / f x = l ^ a * Real.exp (-(a * ∫ s in x..l * x, h s / s)) := by
  have hxpos : 0 < x := lt_of_lt_of_le hr₀ hx
  have hflx : f (l * x) ≠ 0 := ne_of_gt (hpos (l * x) hlx)
  have hfx : f x ≠ 0 := ne_of_gt (hpos x hx)
  rcases le_or_gt 1 l with h1 | h1
  · have hxl : x ≤ l * x := by nlinarith
    have hrep := ode_solution_mul ha hr₀ hderiv hpos hode hmeas hC hx hxl
    rw [hrep, mul_div_cancel_right₀ l (ne_of_gt hxpos)]
    field_simp
  · have hxl : l * x ≤ x := by nlinarith
    have hrep := ode_solution_mul ha hr₀ hderiv hpos hode hmeas hC hlx hxl
    have hratio : x / (l * x) = l⁻¹ := by field_simp
    have hsum : (∫ s in l * x..x, h s / s) + (∫ s in x..l * x, h s / s) = 0 := by
      rw [intervalIntegral.integral_symm x (l * x)]
      ring
    have hprod : Real.exp (-(a * ∫ s in l * x..x, h s / s))
        * Real.exp (-(a * ∫ s in x..l * x, h s / s)) = 1 := by
      rw [← Real.exp_add,
        show -(a * ∫ s in l * x..x, h s / s) + -(a * ∫ s in x..l * x, h s / s)
          = -(a * ((∫ s in l * x..x, h s / s) + ∫ s in x..l * x, h s / s)) by ring,
        hsum, mul_zero, neg_zero, Real.exp_zero]
    have hE : Real.exp (-(a * ∫ s in l * x..x, h s / s)) ≠ 0 := Real.exp_ne_zero _
    have hla : l ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hl a)
    rw [hrep, hratio, Real.inv_rpow hl.le a]
    field_simp
    exact hprod.symm



/-- **The uniform convergence theorem (BGT Theorem 1.2.1) for the ODE class.**
If `a > 0`, `f : (0,∞) → (0,∞)` solves `f' = a (1 - h) f / t` and `h → 0`
is measurable, then for every compact ratio interval `[u,v] ⊂ (0,∞)` and every
`η > 0`, for all sufficiently large `x`,

  `|f (l x) / f x - l ^ a| ≤ η`   for every `l ∈ [u,v]`.

Together with the identity `ratio_eq_of_ode` this is exactly the statement that
`f (l x)/f (x) → l ^ a` *uniformly* in `l` on compact subsets of `(0,∞)`. -/
theorem tendsto_uniformly_ratio_of_ode {f f' h : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, 0 < t → 0 < f t)
    (hode : ∀ t, 0 < t → f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (h0 : Tendsto h atTop (𝓝 0))
    {u v η : ℝ} (hu : 0 < u) (huv : u ≤ v) (hη : 0 < η) :
    ∀ᶠ x in atTop, ∀ l ∈ Icc u v, |f (l * x) / f x - l ^ a| ≤ η := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hM0 : 0 ≤ max |Real.log u| |Real.log v| := le_trans (abs_nonneg _) (le_max_left _ _)
  set M : ℝ := max |Real.log u| |Real.log v| with hM
  -- the two-sided terminal bound
  set δ : ℝ := min (1 / (2 * (a * M + 1))) (η / (8 * (a * M + 1) * (v ^ a + 1))) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hden1 : 0 < 2 * (a * M + 1) := by positivity
  have hden2 : 0 < 8 * (a * M + 1) * (v ^ a + 1) := by positivity
  have hδ1 : a * δ * M ≤ 1 := by
    have hle : δ ≤ 1 / (2 * (a * M + 1)) := min_le_left _ _
    rw [le_div_iff₀ hden1] at hle
    nlinarith [hle, hδpos.le, mul_nonneg ha.le hM0]
  have hδ2 : 2 * (a * δ * M) * v ^ a ≤ η := by
    have hle : δ ≤ η / (8 * (a * M + 1) * (v ^ a + 1)) := min_le_right _ _
    rw [le_div_iff₀ hden2] at hle
    have hvpow : (0:ℝ) < v ^ a := Real.rpow_pos_of_pos hv a
    have haM : 0 ≤ a * M := mul_nonneg ha.le hM0
    have hfac : 2 * (a * M) * v ^ a ≤ 8 * (a * M + 1) * (v ^ a + 1) := by
      nlinarith [haM, hvpow, mul_nonneg haM hvpow.le]
    calc 2 * (a * δ * M) * v ^ a = δ * (2 * (a * M) * v ^ a) := by ring
      _ ≤ δ * (8 * (a * M + 1) * (v ^ a + 1)) :=
          mul_le_mul_of_nonneg_left hfac hδpos.le
      _ = δ * (8 * (a * M + 1) * (v ^ a + 1)) := rfl
      _ ≤ η := by linarith [hle]
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, ∀ t : ℝ, X₀ ≤ t → |h t| ≤ δ := by
    obtain ⟨X₀, hX₀⟩ := Metric.tendsto_atTop.1 h0 δ hδpos
    exact ⟨X₀, fun t ht => by
      have h := hX₀ t ht
      rw [Real.dist_eq, sub_zero, abs_lt] at h
      exact abs_le.2 ⟨le_of_lt h.1, le_of_lt h.2⟩⟩
  set X : ℝ := max (max X₀ (X₀ / u)) 1 with hX
  have hX1 : 1 ≤ X := le_max_right _ _
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX1
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) (le_max_left _ _)
  have hX0u : X₀ / u ≤ X := le_trans (le_max_right _ _) (le_max_left _ _)
  filter_upwards [eventually_ge_atTop X] with x hx
  intro l hl
  obtain ⟨hlu, hlv⟩ := hl
  have hxpos : 0 < x := lt_of_lt_of_le hXpos hx
  have hlpos : 0 < l := lt_of_lt_of_le hu hlu
  have hlx0 : X₀ ≤ l * x := by
    have h1 : X₀ ≤ u * x := by
      have h2 : X₀ / u ≤ x := le_trans hX0u hx
      rw [div_le_iff₀ hu] at h2
      linarith
    nlinarith [hxpos]
  have hxX0 : X₀ ≤ x := le_trans hXX₀ hx
  -- a positive common lower bound for `x` and `l * x` on which `|h| ≤ δ`
  set r : ℝ := min x (l * x) with hrdef
  have hrpos : 0 < r := lt_min hxpos (mul_pos hlpos hxpos)
  have hX0r : X₀ ≤ r := le_min hxX0 hlx0
  have hrx : r ≤ x := min_le_left _ _
  have hrlx : r ≤ l * x := min_le_right _ _
  -- the ratio identity
  have hratio : f (l * x) / f x = l ^ a * Real.exp (-(a * ∫ s in x..l * x, h s / s)) :=
    ratio_eq_of_ode ha hrpos (fun t ht => hderiv t (lt_of_lt_of_le hrpos ht))
      (fun t ht => hpos t (lt_of_lt_of_le hrpos ht))
      (fun t ht => hode t (lt_of_lt_of_le hrpos ht)) hmeas
      (fun t ht => hX₀ t (le_trans hX0r ht)) hrx hlpos hrlx
  -- the oscillation bound
  have hI : |∫ s in x..l * x, h s / s| ≤ δ * |Real.log l| :=
    abs_intervalIntegral_div_le_mul_abs_log hmeas hrpos hrx hlpos hrlx
      (fun t ht => hX₀ t (le_trans hX0r ht))
  have hMl : |Real.log l| ≤ M := by
    have hupper : Real.log l ≤ M :=
      le_trans (le_trans (Real.log_le_log hlpos hlv) (le_abs_self _)) (le_max_right _ _)
    have hlower : -M ≤ Real.log l := by
      have h3 : Real.log u ≤ Real.log l := Real.log_le_log hu hlu
      have h4 : -|Real.log u| ≤ Real.log u := neg_abs_le _
      have h5 : -M ≤ -|Real.log u| := by
        have := le_max_left |Real.log u| |Real.log v|
        linarith
      linarith
    exact abs_le.2 ⟨hlower, hupper⟩
  have hI2 : |∫ s in x..l * x, h s / s| ≤ δ * M :=
    le_trans hI (mul_le_mul_of_nonneg_left hMl hδpos.le)
  have htheta : |a * ∫ s in x..l * x, h s / s| ≤ a * δ * M := by
    rw [abs_mul, abs_of_pos ha]
    nlinarith [hI2, ha, hδpos.le, hM0]
  have hexp : |Real.exp (-(a * ∫ s in x..l * x, h s / s)) - 1| ≤ 2 * (a * δ * M) := by
    have h3 : |-(a * ∫ s in x..l * x, h s / s)| ≤ 1 := by
      rw [abs_neg]
      linarith
    have h4 := Real.abs_exp_sub_one_le h3
    rw [abs_neg] at h4
    linarith
  have hlpa : 0 < l ^ a := Real.rpow_pos_of_pos hlpos a
  have hlvpa : l ^ a ≤ v ^ a := Real.rpow_le_rpow hlpos.le hlv ha.le
  have hvpa : (0:ℝ) < v ^ a := Real.rpow_pos_of_pos hv a
  calc |f (l * x) / f x - l ^ a|
      = |l ^ a * (Real.exp (-(a * ∫ s in x..l * x, h s / s)) - 1)| := by
        rw [hratio]; ring_nf
    _ = l ^ a * |Real.exp (-(a * ∫ s in x..l * x, h s / s)) - 1| := by
        rw [abs_mul, abs_of_pos hlpa]
    _ ≤ v ^ a * (2 * (a * δ * M)) :=
        mul_le_mul hlvpa hexp (abs_nonneg _) hvpa.le
    _ ≤ η := by
        have hcomm : v ^ a * (2 * (a * δ * M)) = 2 * (a * δ * M) * v ^ a := by ring
        rw [hcomm]; exact hδ2

end PercLib.CriticalLRP.Analysis

/-! ### Axiom audit

Run `lake env lean <this file>`; the following must report only the three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms PercLib.CriticalLRP.Analysis.hasPotterBounds_of_ode
#print axioms PercLib.CriticalLRP.Analysis.ratio_eq_of_ode
#print axioms PercLib.CriticalLRP.Analysis.abs_intervalIntegral_div_le_mul_abs_log
#print axioms PercLib.CriticalLRP.Analysis.tendsto_uniformly_ratio_of_ode
#print axioms PercLib.CriticalLRP.Analysis.lemma_I_2_10_of_differentiable
