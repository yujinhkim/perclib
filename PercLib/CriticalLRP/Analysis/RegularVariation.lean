/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Regular variation, logarithmic integrability, and the first ODE lemma of
T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.2.2 (pp. 25-27) and Lemma I.2.12 (p. 26).

Formalized here, with the paper's quantifiers:

* `RegularlyVaryingAtTop f a` : `f` is eventually non-vanishing and
  `f (λ x)/f x → λ ^ a` for every `λ > 0` (paper, p. 25).
* `LogarithmicallyIntegrable h` : `h` measurable and `∫_{r₀}^∞ |h s| ds/s < ∞`.
* `IsLogErrorFunction h` : log-integrable and `h → 0`.
* `ode_solution_mul` : the integrating-factor identity used in the proof of
  Lemma I.2.12, `f R = f r (R/r)^a exp (-a ∫_r^R h s ds/s)`, when
  `f' = a (1-h) f/t` on `[r₀,∞)`.
* `lemma_I_2_12_rv` : Lemma I.2.12, first part.
* `lemma_I_2_12_tendsto` : Lemma I.2.12, second part (`f ∼ A r^a`).

Note on hypotheses: the paper's proof only needs the fundamental theorem of
calculus for `log ∘ f`; the only regularity needed of the error function `h` is
measurability (for the interval integrals) and local boundedness on `[r₀,∞)`.
No continuity of `h` or of `f'` is assumed.
-/
module

public import Mathlib

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

/-! ### Regular variation and logarithmic integrability -/

/-- **Regular variation at `∞` of index `a`** (paper, p. 25): `f` is eventually
non-vanishing and `f (λ x) / f x → λ ^ a` for every `λ > 0`. -/
def RegularlyVaryingAtTop (f : ℝ → ℝ) (a : ℝ) : Prop :=
  (∀ᶠ x in atTop, f x ≠ 0) ∧
    ∀ l : ℝ, 0 < l → Tendsto (fun x => f (l * x) / f x) atTop (𝓝 (l ^ a))

/-- Slowly varying = regularly varying of index `0`. -/
def SlowlyVaryingAtTop (f : ℝ → ℝ) : Prop := RegularlyVaryingAtTop f 0

/-- **Logarithmic integrability** (paper, p. 26): `h` is measurable and
`∫_{r₀}^∞ |h(r)| dr/r < ∞` for some `r₀ > 0`. -/
def LogarithmicallyIntegrable (h : ℝ → ℝ) : Prop :=
  Measurable h ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ IntegrableOn (fun r => |h r| / r) (Ioi r₀)

/-- A **logarithmically integrable error function**: log-integrable and `→ 0`. -/
def IsLogErrorFunction (h : ℝ → ℝ) : Prop :=
  LogarithmicallyIntegrable h ∧ Tendsto h atTop (𝓝 0)

/-! ### Interval integrability helpers -/

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

/-- If `|g t| ≤ C` for `t ≥ r`, then `t ↦ g t / t` is interval integrable on `[r,R]`
(with `0 < r ≤ R`). -/
theorem intervalIntegrable_div_of_bounded {g : ℝ → ℝ} {r R C : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hmeas : Measurable g) (hC : ∀ t, r ≤ t → |g t| ≤ C) :
    IntervalIntegrable (fun t => g t / t) volume r R := by
  refine intervalIntegrable_of_bound (C := |C| / r) ?_ ?_
  · exact (hmeas.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIcc] with t ht
    rw [uIcc_of_le hrR] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hr ht.1
    have h1 : |g t| ≤ |C| := le_trans (hC t ht.1) (le_abs_self C)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul h1 (by simpa [one_div] using one_div_le_one_div_of_le hr ht.1)
      (by positivity) (abs_nonneg C)

/-! ### The integrating-factor identity -/

/-- **The integrating-factor identity** behind Lemma I.2.12: if `f > 0` is
differentiable on `[r₀,∞)` and `f' = a (1 - h) f / t` there, with `h` measurable
and bounded on `[r₀,∞)`, then for `r₀ ≤ r ≤ R`
`log (f R) - log (f r) = a log (R/r) - a ∫_r^R h s ds/s`. -/
theorem ode_log_identity {f f' h : ℝ → ℝ} {a r₀ C : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hode : ∀ t, r₀ ≤ t → f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    {r R : ℝ} (hr : r₀ ≤ r) (hrR : r ≤ R) :
    Real.log (f R) - Real.log (f r) = a * Real.log (R / r) - a * ∫ s in r..R, h s / s := by
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR
  -- integrability of the three pieces
  have hint1 : IntervalIntegrable (fun t => (a * (1 - h t)) / t) volume r R :=
    intervalIntegrable_div_of_bounded hr0 hrR ((measurable_const.sub hmeas).const_mul a)
      (fun t ht => by
        have hCt : |h t| ≤ C := hC t (le_trans hr ht)
        have h2 : |h t| ≤ |C| := le_trans hCt (le_abs_self C)
        calc |a * (1 - h t)| = |a| * |1 - h t| := abs_mul _ _
          _ ≤ |a| * (1 + |C|) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
              calc |1 - h t| ≤ 1 + |h t| := by
                    have habs := abs_sub (1 : ℝ) (h t)
                    rwa [abs_one] at habs
                _ ≤ 1 + |C| := by linarith)
  have hint2 : IntervalIntegrable (fun t => f' t / f t) volume r R :=
    hint1.congr (fun t ht => by
      rw [uIoc_of_le hrR] at ht
      have htr : r₀ ≤ t := le_trans hr ht.1.le
      have hf : f t ≠ 0 := ne_of_gt (hpos t htr)
      rw [hode t htr]
      field_simp)
  have hlog : ∫ t in r..R, f' t / f t = Real.log (f R) - Real.log (f r) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => by
        rw [uIcc_of_le hrR] at ht
        exact (hderiv t (le_trans hr ht.1)).log (ne_of_gt (hpos t (le_trans hr ht.1))))
      hint2
  have hpt : ∀ t ∈ uIcc r R, f' t / f t = a * (1 / t) - a * (h t / t) := by
    intro t ht
    rw [uIcc_of_le hrR] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hr0 ht.1)
    have htr : r₀ ≤ t := le_trans hr ht.1
    have hf : f t ≠ 0 := ne_of_gt (hpos t htr)
    rw [hode t htr]
    field_simp
  have hintA : IntervalIntegrable (fun t => a * (1 / t)) volume r R := by
    have h := intervalIntegrable_div_of_bounded (C := |a|) (g := fun _ => a) hr0 hrR
      measurable_const (fun t _ => le_rfl)
    refine h.congr (fun t _ => by ring)
  have hintB : IntervalIntegrable (fun t => a * (h t / t)) volume r R := by
    have h := intervalIntegrable_div_of_bounded (C := |a| * |C|) (g := fun t => a * h t) hr0 hrR
      (hmeas.const_mul a) (fun t ht => by
        have hCt : |h t| ≤ C := hC t (le_trans hr ht)
        calc |a * h t| = |a| * |h t| := abs_mul _ _
          _ ≤ |a| * |C| := mul_le_mul_of_nonneg_left (le_trans hCt (le_abs_self C)) (abs_nonneg a))
    refine h.congr (fun t _ => by ring)
  have heval : ∫ t in r..R, f' t / f t
      = a * Real.log (R / r) - a * ∫ s in r..R, h s / s := by
    rw [intervalIntegral.integral_congr hpt,
      intervalIntegral.integral_sub hintA hintB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_one_div_of_pos hr0 hR0]
  rw [← heval, hlog]

/-- **Explicit solution** of `f' = a (1 - h) f / t` (the formula displayed in
the proof of Lemma I.2.12): for `r₀ ≤ r ≤ R`,
`f R = f r (R/r)^a exp (-a ∫_r^R h s ds/s)`. -/
theorem ode_solution_mul {f f' h : ℝ → ℝ} {a r₀ C : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hode : ∀ t, r₀ ≤ t → f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    {r R : ℝ} (hr : r₀ ≤ r) (hrR : r ≤ R) :
    f R = f r * (R / r) ^ a * Real.exp (-(a * ∫ s in r..R, h s / s)) := by
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR
  have hfr : 0 < f r := hpos r hr
  have hfR : 0 < f R := hpos R (le_trans hr hrR)
  have hlog := ode_log_identity ha hr₀ hderiv hpos hode hmeas hC hr hrR
  have hlog' : Real.log (f R)
      = Real.log (f r) + a * Real.log (R / r) - a * ∫ s in r..R, h s / s := by linarith
  have hratio : 0 < R / r := div_pos hR0 hr0
  calc f R = Real.exp (Real.log (f R)) := (Real.exp_log hfR).symm
    _ = Real.exp (Real.log (f r) + a * Real.log (R / r) - a * ∫ s in r..R, h s / s) := by
        rw [hlog']
    _ = Real.exp (Real.log (f r)) * Real.exp (a * Real.log (R / r))
          * Real.exp (-(a * ∫ s in r..R, h s / s)) := by
        rw [show Real.log (f r) + a * Real.log (R / r) - a * ∫ s in r..R, h s / s
              = Real.log (f r) + (a * Real.log (R / r) + -(a * ∫ s in r..R, h s / s)) by ring,
          Real.exp_add, Real.exp_add, Real.exp_neg]
        ring
    _ = f r * (R / r) ^ a * Real.exp (-(a * ∫ s in r..R, h s / s)) := by
        rw [Real.exp_log hfr, mul_comm a (Real.log (R / r)), ← Real.rpow_def_of_pos hratio a]

/-! ### Lemma I.2.12 -/

/-- Bound on `|∫_x^y h s ds/s|` by `δ log (y/x)` when `|h| ≤ δ` on `[x,y]`,
`0 < x ≤ y`. -/
theorem abs_intervalIntegral_div_le {h : ℝ → ℝ} {δ x y : ℝ}
    (hmeas : Measurable h) (hx : 0 < x) (hxy : x ≤ y) (hbdd : ∀ s, x ≤ s → |h s| ≤ δ) :
    |∫ s in x..y, h s / s| ≤ δ * Real.log (y / x) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hδ : 0 ≤ δ := le_trans (abs_nonneg (h x)) (hbdd x le_rfl)
  have hInt1 : IntervalIntegrable (fun s => h s / s) volume x y :=
    intervalIntegrable_div_of_bounded hx hxy hmeas hbdd
  have hInt2 : IntervalIntegrable (fun s => |h s| / s) volume x y :=
    intervalIntegrable_div_of_bounded hx hxy hmeas.abs (fun s hs => by
      rw [abs_abs]; exact hbdd s hs)
  have hInt3 : IntervalIntegrable (fun s => δ * (1 / s)) volume x y := by
    have h := intervalIntegrable_div_of_bounded (C := |δ|) (g := fun _ => δ) hx hxy
      measurable_const (fun s _ => le_rfl)
    exact h.congr (fun s _ => by ring)
  calc |∫ s in x..y, h s / s|
      ≤ ∫ s in x..y, |h s / s| := intervalIntegral.abs_integral_le_integral_abs hxy
    _ = ∫ s in x..y, |h s| / s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hxy] at hs
        have hs0 : 0 < s := lt_of_lt_of_le hx hs.1
        show |h s / s| = |h s| / s
        rw [abs_div, abs_of_pos hs0]
    _ ≤ ∫ s in x..y, δ * (1 / s) := by
        apply intervalIntegral.integral_mono_on hxy hInt2 hInt3
        intro s hs
        have hs0 : 0 < s := lt_of_lt_of_le hx hs.1
        rw [mul_one_div, div_le_iff₀ hs0, div_mul_cancel₀ _ hs0.ne']
        exact hbdd s hs.1
    _ = δ * Real.log (y / x) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hx hy]

/-- The key oscillation estimate: if `h` is measurable and `h → 0`, then
`∫_x^{λ x} h s ds/s → 0` along `x → ∞`. -/
theorem tendsto_intervalIntegral_div_of_tendsto_zero {h : ℝ → ℝ}
    (hmeas : Measurable h) (h0 : Tendsto h atTop (𝓝 0)) (l : ℝ) (hl : 0 < l) :
    Tendsto (fun x : ℝ => ∫ s in x..l * x, h s / s) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (|Real.log l| + 1) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨X, hX⟩ : ∃ X : ℝ, ∀ t : ℝ, X ≤ t → |h t| ≤ δ := by
    obtain ⟨X, hX⟩ := Metric.tendsto_atTop.1 h0 δ hδpos
    exact ⟨X, fun t ht => by
      have h := hX t ht
      rw [Real.dist_eq, sub_zero, abs_lt] at h
      exact abs_le.2 ⟨le_of_lt h.1, le_of_lt h.2⟩⟩
  refine ⟨max (max X (X / l) + 1) 1, fun x hx => ?_⟩
  have hstep : max X (X / l) + 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxX : X ≤ x := by
    have h1 : X ≤ max X (X / l) := le_max_left _ _
    linarith
  have hx1 : (1:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hxlX : X ≤ l * x := by
    have h2 : X / l ≤ max X (X / l) := le_max_right _ _
    have h3 : l * (X / l) = X := by field_simp
    nlinarith
  have hδabs : δ * |Real.log l| < ε := by
    have h1 : 0 ≤ |Real.log l| := abs_nonneg _
    rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, sub_zero]
  rcases le_or_gt x (l * x) with hcase | hcase
  · have hl1 : 1 ≤ l := by nlinarith
    have hbdd : ∀ s, x ≤ s → |h s| ≤ δ := fun s hs => hX s (le_trans hxX hs)
    have h1 := abs_intervalIntegral_div_le hmeas hx0 hcase hbdd
    have h2 : Real.log (l * x / x) = Real.log l := by
      rw [mul_div_cancel_right₀ l hx0.ne']
    rw [h2] at h1
    calc |∫ s in x..l * x, h s / s| ≤ δ * Real.log l := h1
      _ = δ * |Real.log l| := by rw [abs_of_nonneg (Real.log_nonneg hl1)]
      _ < ε := hδabs
  · have hl1 : l < 1 := by nlinarith
    have hbdd : ∀ s, l * x ≤ s → |h s| ≤ δ := fun s hs => hX s (le_trans hxlX hs)
    have h1 := abs_intervalIntegral_div_le hmeas (by positivity : (0:ℝ) < l * x)
      (le_of_lt hcase) hbdd
    have h2 : Real.log (x / (l * x)) = -Real.log l := by
      rw [show x / (l * x) = l⁻¹ by field_simp, Real.log_inv]
    rw [h2] at h1
    have hsymm : ∫ s in x..l * x, h s / s = -∫ s in l * x..x, h s / s :=
      intervalIntegral.integral_symm (l * x) x
    rw [hsymm, abs_neg]
    calc |∫ s in l * x..x, h s / s| ≤ δ * -Real.log l := h1
      _ = δ * |Real.log l| := by rw [abs_of_neg (Real.log_neg hl hl1)]
      _ < ε := hδabs

/-- **Lemma I.2.12, first part.** If `f : (0,∞) → (0,∞)` is differentiable on
`[r₀,∞)` and `f'(r) = a (1 - h(r)) r⁻¹ f(r)` there, where `h` is measurable and
`h(r) → 0`, then `f` is regularly varying of index `a`. -/
theorem lemma_I_2_12_rv {f f' h : ℝ → ℝ} {a r₀ : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hode : ∀ t, r₀ ≤ t → f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (h0 : Tendsto h atTop (𝓝 0)) :
    RegularlyVaryingAtTop f a := by
  obtain ⟨r₁, hr₁, hC⟩ : ∃ r₁ : ℝ, r₀ ≤ r₁ ∧ ∀ t : ℝ, r₁ ≤ t → |h t| ≤ 1 := by
    obtain ⟨X, hX⟩ := Metric.tendsto_atTop.1 h0 1 one_pos
    refine ⟨max r₀ X, le_max_left _ _, fun t ht => ?_⟩
    have h := hX t (le_trans (le_max_right r₀ X) ht)
    rw [Real.dist_eq, sub_zero, abs_lt] at h
    exact abs_le.2 ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le hr₀ hr₁
  have hderiv' : ∀ t, r₁ ≤ t → HasDerivAt f (f' t) t := fun t ht => hderiv t (le_trans hr₁ ht)
  have hpos' : ∀ t, r₁ ≤ t → 0 < f t := fun t ht => hpos t (le_trans hr₁ ht)
  have hode' : ∀ t, r₁ ≤ t → f' t = a * (1 - h t) * f t / t :=
    fun t ht => hode t (le_trans hr₁ ht)
  -- the case `l ≥ 1`
  have hbase : ∀ l : ℝ, 1 ≤ l →
      Tendsto (fun x => f (l * x) / f x) atTop (𝓝 (l ^ a)) := by
    intro l hl
    have hevent : ∀ᶠ x in atTop, f (l * x) / f x
        = l ^ a * Real.exp (-(a * ∫ s in x..l * x, h s / s)) := by
      filter_upwards [eventually_ge_atTop r₁, eventually_ge_atTop (r₁ / l)] with x hx hxl
      have hlpos : 0 < l := lt_of_lt_of_le one_pos hl
      have hlx : r₁ ≤ l * x := by
        have h3 : l * (r₁ / l) = r₁ := by field_simp
        have h4 : l * (r₁ / l) ≤ l * x := by
          apply mul_le_mul_of_nonneg_left hxl hlpos.le
        linarith
      have hxle : x ≤ l * x := by
        have hx0 : 0 < x := lt_of_lt_of_le hr₁pos hx
        nlinarith
      have h1 := ode_solution_mul ha hr₁pos hderiv' hpos' hode' hmeas hC hx hxle
      have hfx : f x ≠ 0 := ne_of_gt (hpos' x hx)
      have hx0 : 0 < x := lt_of_lt_of_le hr₁pos hx
      have hlxx : l * x / x = l := by rw [mul_div_cancel_right₀ l hx0.ne']
      rw [h1, hlxx, mul_assoc, mul_div_cancel_left₀ _ hfx]
    have hlim : Tendsto (fun x : ℝ => l ^ a * Real.exp (-(a * ∫ s in x..l * x, h s / s)))
        atTop (𝓝 (l ^ a)) := by
      have hosc := tendsto_intervalIntegral_div_of_tendsto_zero hmeas h0 l
        (lt_of_lt_of_le one_pos hl)
      have h2 : Tendsto (fun x : ℝ => -(a * ∫ s in x..l * x, h s / s)) atTop (𝓝 0) := by
        simpa using (hosc.const_mul a).neg
      have h3 : Tendsto (fun x : ℝ => Real.exp (-(a * ∫ s in x..l * x, h s / s)))
          atTop (𝓝 (Real.exp 0)) :=
        (Real.continuous_exp.tendsto 0).comp h2
      rw [Real.exp_zero] at h3
      simpa using h3.const_mul (l ^ a)
    exact hlim.congr' (Filter.EventuallyEq.symm hevent)
  constructor
  · filter_upwards [eventually_ge_atTop r₁] with x hx
    exact ne_of_gt (hpos' x hx)
  · intro l hl
    rcases le_or_gt 1 l with hl1 | hl1
    · exact hbase l hl1
    · -- `0 < l < 1`: apply the case `l ≥ 1` to `l⁻¹` and invert
      have hlinv : 1 ≤ l⁻¹ := by
        rw [le_inv_comm₀ one_pos hl]
        simpa using hl1.le
      have h := hbase l⁻¹ hlinv
      have hcomp : Tendsto (fun x : ℝ => f (l⁻¹ * (l * x)) / f (l * x)) atTop
          (𝓝 ((l⁻¹) ^ a)) :=
        h.comp ((tendsto_const_mul_atTop_of_pos hl).2 tendsto_id)
      have hcomp' : Tendsto (fun x : ℝ => f x / f (l * x)) atTop (𝓝 ((l⁻¹) ^ a)) := by
        refine hcomp.congr' ?_
        filter_upwards with x
        rw [show l⁻¹ * (l * x) = x by field_simp]
      have hinv := hcomp'.inv₀ (by positivity)
      have hgoal : (l⁻¹ : ℝ) ^ a = (l ^ a)⁻¹ := Real.inv_rpow hl.le a
      rw [hgoal] at hinv
      have hfin : Tendsto (fun x => (f x / f (l * x))⁻¹) atTop (𝓝 (l ^ a)) := by
        simpa using hinv
      refine hfin.congr' ?_
      filter_upwards with x
      exact inv_div (f x) (f (l * x))

/-- **Lemma I.2.12, second part.** If in addition `h` is logarithmically
integrable, then `f(r) ∼ A r^a` for a constant `A > 0`. -/
theorem lemma_I_2_12_tendsto {f f' h : ℝ → ℝ} {a r₀ C : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hode : ∀ t, r₀ ≤ t → f' t = a * (1 - h t) * f t / t)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (hlog : LogarithmicallyIntegrable h) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A) := by
  obtain ⟨r₂, hr₂, hint⟩ := hlog.2
  set R₀ : ℝ := max r₀ r₂ with hR₀def
  have hR₀ : 0 < R₀ := lt_of_lt_of_le hr₀ (le_max_left _ _)
  have hr₀R₀ : r₀ ≤ R₀ := le_max_left _ _
  have hR₀r₂ : r₂ ≤ R₀ := le_max_right _ _
  have hint' : IntegrableOn (fun s => h s / s) (Ioi R₀) := by
    have h0 := hint.mono_set (Ioi_subset_Ioi hR₀r₂)
    refine h0.mono' ?_ ?_
    · exact (hmeas.div measurable_id).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := lt_of_lt_of_le hR₀ (le_of_lt hs)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hs0]
  set L : ℝ := ∫ s in Ioi R₀, h s / s with hLdef
  have hfR₀ : 0 < f R₀ := hpos R₀ hr₀R₀
  refine ⟨f R₀ * R₀ ^ (-a) * Real.exp (-(a * L)), by positivity, ?_⟩
  have hlim : Tendsto (fun r : ℝ => f R₀ * R₀ ^ (-a) * Real.exp (-(a * ∫ s in R₀..r, h s / s)))
      atTop (𝓝 (f R₀ * R₀ ^ (-a) * Real.exp (-(a * L)))) := by
    have hIntLim : Tendsto (fun r : ℝ => ∫ s in R₀..r, h s / s) atTop (𝓝 L) :=
      intervalIntegral_tendsto_integral_Ioi R₀ hint' tendsto_id
    have h2 : Tendsto (fun r : ℝ => Real.exp (-(a * ∫ s in R₀..r, h s / s)))
        atTop (𝓝 (Real.exp (-(a * L)))) := by
      have h3 : Tendsto (fun r : ℝ => -(a * ∫ s in R₀..r, h s / s)) atTop (𝓝 (-(a * L))) := by
        simpa using (hIntLim.const_mul a).neg
      exact (Real.continuous_exp.tendsto (-(a * L))).comp h3
    exact h2.const_mul (f R₀ * R₀ ^ (-a))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop R₀] with r hr
  have hr0 : 0 < r := lt_of_lt_of_le hR₀ hr
  have h1 := ode_solution_mul ha hr₀ hderiv hpos hode hmeas hC hr₀R₀ hr
  rw [h1, Real.div_rpow hr0.le hR₀.le, Real.rpow_neg hR₀.le]
  field_simp


/-- **Lemma I.2.12 in the paper's form.**  If `f : (0,∞) → (0,∞)` is differentiable on
`[r₀,∞)`, `f'` is continuous on `[r₀,∞)`, and `f'(r) ∼ a r⁻¹ f(r)` (i.e.
`r f'(r)/(a f(r)) → 1`), then `f` is regularly varying of index `a`.

The continuity of `f'` is used only to make the error function
`h = 1 - r f'/(a f)` measurable; measurability of `f'` on the tail would suffice. -/
theorem lemma_I_2_12_rv' {f f' : ℝ → ℝ} {a r₀ : ℝ}
    (ha : 0 < a) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hcont : ContinuousOn f' (Ici r₀))
    (hasy : Tendsto (fun t => t * f' t / (a * f t)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f a := by
  -- the error function `h = 1 - r f'/(a f)` on the tail, `0` elsewhere
  set g : ℝ → ℝ := fun t => 1 - t * f' t / (a * f t) with hg
  have hcontf : ContinuousOn f (Ici r₀) := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hcontg : ContinuousOn g (Ici r₀) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₀ hx)
    have hfx : f x ≠ 0 := ne_of_gt (hpos x hx)
    have h1 : ContinuousWithinAt f' (Ici r₀) x := hcont x hx
    have h2 : ContinuousWithinAt f (Ici r₀) x := hcontf x hx
    have h3 : ContinuousWithinAt (fun t => t * f' t / (a * f t)) (Ici r₀) x := by
      apply ContinuousWithinAt.div
      · exact continuousWithinAt_id.mul h1
      · exact continuousWithinAt_const.mul h2
      · exact mul_ne_zero (ne_of_gt ha) hfx
    exact continuousWithinAt_const.sub h3
  have hmeas : Measurable ((Ici r₀).piecewise g 0) :=
    ContinuousOn.measurable_piecewise hcontg continuousOn_const measurableSet_Ici
  have hone : ∀ t : ℝ, t ∈ Ici r₀ → g t = 1 - t * f' t / (a * f t) := fun t ht => rfl
  -- `h → 0`
  have h0 : Tendsto ((Ici r₀).piecewise g 0) atTop (𝓝 0) := by
    have h1 : Tendsto g atTop (𝓝 (1 - 1)) := by
      have := hasy.const_sub 1
      simpa [hg] using this
    rw [sub_self] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop r₀] with t ht
    have ht' : t ∈ Ici r₀ := ht
    simp only [Set.piecewise, ht', ite_true]
  -- the ODE holds with this `h`
  have hode : ∀ t, r₀ ≤ t → f' t = a * (1 - (Ici r₀).piecewise g 0 t) * f t / t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hr₀ ht)
    have hft : f t ≠ 0 := ne_of_gt (hpos t ht)
    have ht' : t ∈ Ici r₀ := ht
    have hpt : (Ici r₀).piecewise g 0 t = 1 - t * f' t / (a * f t) := by
      simp only [Set.piecewise, ht', ite_true, hg]
    rw [hpt]
    field_simp
    ring
  exact lemma_I_2_12_rv ha hr₀ hderiv hpos hode hmeas h0

end PercLib.CriticalLRP.Analysis
