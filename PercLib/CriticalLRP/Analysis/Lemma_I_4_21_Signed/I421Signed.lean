/- Integrated from independently rebuilt Ultramath work.
Production base 9b516d9ff11bc919f2687249e032ecd08f68166b.
Scratch source: repository-root .ultramath/smwwnvyp3/m1/I421Signed.lean.
-/

/-
# Lemma I.4.21 for a signed solution `f`

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.21 (pp. 47-48).

The paper assumes only that `f` is differentiable, not that it is positive:
given `a > 0`, a measurable regularly varying `h` of index `b > a` and
`f'(r) ~ (a f(r) + h(r))/r`, it concludes `f(r) ~ h(r)/(b-a)` and that `f` is
regularly varying of index `b`.

`PercLib.CriticalLRP.Analysis.lemma_I_4_21_tendsto_of_hasDerivAt` and its
regular-variation companion prove this for positive `f`.  Here positivity of
`f` is removed from every hypothesis and is instead *derived*, together with
eventual non-vanishing of `f`, from the other hypotheses.

The single point of substance is the construction of the shared error: the
quotient `f' r / ((a f r + h r)/r)` equals `0` whenever `a f r + h r = 0`
(Lean's division by zero), so the hypothesis that the quotient tends to `1`
*itself* forces `a f r + h r ≠ 0` eventually.  That is the only non-vanishing
required; `f` may be negative on an initial interval, and indeed is in the
example at the end of this file.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_4_21

/-!
# Contents

* `exists_shared_error_of_tendsto_signed` — the shared error of Lemma I.4.21
  with only `Measurable h`, no positivity of `f` or `h`, and the non-vanishing
  `a f + h ≠ 0` derived from the limit and reported;
* `exists_shared_error_of_tendsto`, `exists_shared_error_of_tendsto'` — the
  same with the paper's `RVPosData h b` on `h`, the second with exactly the
  production conclusion (drop-in replacement);
* `lemma_I_4_21_tendsto_of_hasDerivAt` — `f(r) ~ h(r)/(b-a)`, signed `f`;
* `lemma_I_4_21_regularlyVarying_of_hasDerivAt` — `f` is regularly varying of
  index `b`;
* `lemma_I_4_21_eventually_pos_of_hasDerivAt` — eventual positivity *derived*;
* `lemma_I_4_21_signed` — all conclusions at once;
* `lemma_I_4_21_of_differentiableAt` — the paper's own quantifiers, with
  `deriv f` and no separate `f'`;
* `lemma_I_5_5_branch_of_lt` — the `a < b` branch of Lemma I.5.5 without
  positivity of `f`;
* `tendsto_two_term_error_of_driving_ode` — the two-term error `(r f' - a f)/h`
  of Lemma I.5.26, with `A = 1`;
* `signed_hypotheses_with_sign_changing_f` — the hypotheses hold for an `f`
  that is negative on `(0,1)`, so the generalization is strict.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis.I421Signed

/-! ## The shared error, without positivity of `f` -/

/-- **The measurable shared error of Lemma I.4.21 for a signed `f`.**

From `f'(r) ~ (a f(r) + h(r))/r` alone (plus differentiability of `f` and
measurability of `h`) there is a measurable `δ → 0` with `|δ| ≤ 1` and
`f' = (1 - δ) (a f + h)/r` on a tail `[r₀, ∞)` that also starts above `T`.
Unlike the positive-`f` version in `Analysis/Lemma_I_4_21.lean`, no positivity
of `f` or of `h` is assumed, and the non-vanishing `a f x + h x ≠ 0` needed to
divide by the source coefficient is *derived* (from the limit) and reported.
The construction itself does not use `a > 0`; that hypothesis is kept only to
match the source and the existing statement. -/
theorem exists_shared_error_of_tendsto_signed {f f' h : ℝ → ℝ} {a T : ℝ}
    (ha : 0 < a) (hm : Measurable h)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    ∃ r₀ δ, 0 < r₀ ∧ 1 ≤ r₀ ∧ T ≤ r₀ ∧ Measurable δ ∧
      Tendsto δ atTop (𝓝 0) ∧ (∀ x, r₀ ≤ x → |δ x| ≤ 1) ∧
      (∀ x, r₀ ≤ x → a * f x + h x ≠ 0) ∧
      ∀ x, r₀ ≤ x → f' x = (1 - δ x) * (a * f x + h x) / x := by
  let f₀ : ℝ → ℝ := fun r => if 0 < r then f r else 0
  have hf0m : Measurable f₀ := measurable_ite_pos_of_hasDerivAt hderiv
  have hf0eq : ∀ x, 0 < x → f₀ x = f x := by intro x hx; simp [f₀, hx]
  have hf0d : ∀ x, 0 < x → HasDerivAt f₀ (f' x) x := by
    intro x hx
    apply (hderiv x hx).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp [f₀, Set.mem_Ioi.1 hy]
  -- The degenerate case `a f x + h x = 0` is harmless: both sides vanish.
  have hquot : ∀ x, 0 < x →
      f' x / ((a * f x + h x) / x) = deriv f₀ x * x / (a * f₀ x + h x) := by
    intro x hx
    rw [(hf0d x hx).deriv, hf0eq x hx]
    by_cases hD : a * f x + h x = 0
    · rw [hD, zero_div, div_zero, div_zero]
    · field_simp [hD, ne_of_gt hx]
  have hq : Tendsto (fun r => deriv f₀ r * r / (a * f₀ r + h r)) atTop (𝓝 1) := by
    apply hasym.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hquot x hx
  have hraw0 : Tendsto (fun r => 1 - deriv f₀ r * r / (a * f₀ r + h r)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hq
  let δ : ℝ → ℝ := (Ioi 0).indicator (fun r => 1 - deriv f₀ r * r / (a * f₀ r + h r))
  have hδm : Measurable δ := by
    apply Measurable.indicator _ measurableSet_Ioi
    exact measurable_const.sub (((measurable_deriv f₀).mul measurable_id).div
      ((measurable_const.mul hf0m).add hm))
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    apply hraw0.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [δ, hx]
  -- The limit `1` forces the source coefficient to be non-zero eventually.
  have hane : ∀ᶠ x in atTop, a * f x + h x ≠ 0 := by
    have h1 : ∀ᶠ x in atTop, 0 < f' x / ((a * f x + h x) / x) :=
      hasym.eventually (eventually_gt_nhds zero_lt_one)
    filter_upwards [h1] with x hx hzero
    rw [hzero, zero_div, div_zero] at hx
    exact lt_irrefl 0 hx
  obtain ⟨B, hB⟩ := Metric.tendsto_atTop.1 hδ0 1 one_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hane
  let R₀ : ℝ := max (max (max 1 T) B) N
  have hR₀1 : 1 ≤ R₀ :=
    le_trans (le_max_left 1 T) (le_trans (le_max_left _ B) (le_max_left _ N))
  have hR₀T : T ≤ R₀ :=
    le_trans (le_max_right 1 T) (le_trans (le_max_left _ B) (le_max_left _ N))
  have hR₀B : B ≤ R₀ := le_trans (le_max_right (max 1 T) B) (le_max_left _ N)
  have hR₀N : N ≤ R₀ := le_max_right _ _
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le one_pos hR₀1
  refine ⟨R₀, δ, hR₀pos, hR₀1, hR₀T, hδm, hδ0, ?_, ?_, ?_⟩
  · intro x hx
    have hb := hB x (le_trans hR₀B hx)
    rw [Real.dist_eq, sub_zero] at hb
    linarith
  · intro x hx
    exact hN x (le_trans hR₀N hx)
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hR₀pos hx
    have hden : a * f x + h x ≠ 0 := hN x (le_trans hR₀N hx)
    have hd : deriv f₀ x = f' x := (hf0d x hx0).deriv
    have hdx : δ x = 1 - deriv f₀ x * x / (a * f₀ x + h x) := by
      simp [δ, hx0]
    rw [hdx, hf0eq x hx0, hd]
    field_simp [hden, ne_of_gt hx0]
    ring

/-! ## The source-shaped statement

`h` is a measurable regularly varying function of index `b`; the tail starts
above `D.threshold`.  This is the paper's hypothesis on `h`. -/

/-- **The shared error of Lemma I.4.21, with the paper's hypotheses on `h`.**

This is `Analysis.exists_shared_error_of_tendsto` with the two positivity
hypotheses (`0 < h` and `0 < f` on all of `(0,∞)`) removed, and with the
non-vanishing of the source coefficient `a f x + h x` derived and reported.
Only `D.measurable_f` is used about `h`. -/
theorem exists_shared_error_of_tendsto {f f' : ℝ → ℝ} {h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    ∃ r₀ δ, 0 < r₀ ∧ 1 ≤ r₀ ∧ D.threshold ≤ r₀ ∧ Measurable δ ∧
      Tendsto δ atTop (𝓝 0) ∧ (∀ x, r₀ ≤ x → |δ x| ≤ 1) ∧
      (∀ x, r₀ ≤ x → a * f x + h x ≠ 0) ∧
      ∀ x, r₀ ≤ x → f' x = (1 - δ x) * (a * f x + h x) / x :=
  exists_shared_error_of_tendsto_signed (T := D.threshold) ha D.measurable_f hderiv hasym

/-- **Drop-in replacement** for the positive-`f`
`Analysis.exists_shared_error_of_tendsto`: the same conclusion, with no
positivity hypothesis on `f` (or on `h`). -/
theorem exists_shared_error_of_tendsto' {f f' : ℝ → ℝ} {h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a : ℝ} (ha : 0 < a)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    ∃ r₀ δ, 0 < r₀ ∧ 1 ≤ r₀ ∧ D.threshold ≤ r₀ ∧ Measurable δ ∧
      Tendsto δ atTop (𝓝 0) ∧ (∀ x, r₀ ≤ x → |δ x| ≤ 1) ∧
      ∀ x, r₀ ≤ x → f' x = (1 - δ x) * (a * f x + h x) / x := by
  obtain ⟨r₀, δ, h1, h2, h3, h4, h5, h6, -, h7⟩ :=
    exists_shared_error_of_tendsto D ha hderiv hasym
  exact ⟨r₀, δ, h1, h2, h3, h4, h5, h6, h7⟩

/-! ## The asymptotic ratio and regular variation, for signed `f` -/

/-- **Lemma I.4.21, asymptotic-ratio form, with no positivity of `f`.**

`a > 0`, `a < b`, `h` measurable regularly varying of index `b`, `f`
differentiable with `f'(r) ~ (a f(r) + h(r))/r`; then `f(r) ~ h(r)/(b-a)`.
The signed `f` may be negative on an initial interval. -/
theorem lemma_I_4_21_tendsto_of_hasDerivAt {f f' : ℝ → ℝ} {h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (h r / (b - a))) atTop (𝓝 1) := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  obtain ⟨r₀, δ, hr₀, hr₀1, hrD, hδm, hδ0, hδ1, hode⟩ :=
    exists_shared_error_of_tendsto' D ha hderiv hasym
  have hlim := tendsto_div_of_driving_ode D ha hab hr₀ hr₀1 hrD
    (fun x hx => hderiv x (lt_of_lt_of_le hr₀ hx))
    hδm hδ0 hδ1 hode
  have hmul := hlim.const_mul (b - a)
  have hmul' : (b - a) * (1 / (b - a)) = 1 := by field_simp [hne]
  rw [hmul'] at hmul
  apply hmul.congr'
  filter_upwards [D.rv.1] with r hr
  field_simp [hr, hne]

/-- **Lemma I.4.21, regular-variation conclusion, with no positivity of `f`.**
The signed `f` is regularly varying of index `b`. -/
theorem lemma_I_4_21_regularlyVarying_of_hasDerivAt {f f' : ℝ → ℝ} {h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f b := by
  have hne : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hGrv : RegularlyVaryingAtTop (fun r => h r / (b - a)) b := by
    constructor
    · filter_upwards [D.rv.1] with r hr
      exact div_ne_zero hr hne
    · intro l hl
      apply (D.rv.2 l hl).congr'
      filter_upwards [D.rv.1] with r hr
      field_simp [hr, hne]
  exact RegularlyVaryingAtTop.of_tendsto_div hGrv
    (lemma_I_4_21_tendsto_of_hasDerivAt D ha hab hderiv hasym)

/-- **Eventual positivity is derived, not assumed.**  Under the signed
hypotheses of Lemma I.4.21, with `b > a` and `h` eventually positive, the
solution `f` is eventually positive: this is the conclusion `f ~ h/(b-a)` with
`b - a > 0`, and it is exactly the positivity that the positive-`f` version of
the lemma takes as a hypothesis. -/
theorem lemma_I_4_21_eventually_pos_of_hasDerivAt {f f' : ℝ → ℝ} {h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    ∀ᶠ r in atTop, 0 < f r := by
  have hlim := lemma_I_4_21_tendsto_of_hasDerivAt D ha hab hderiv hasym
  have h1 : ∀ᶠ r in atTop, 0 < f r / (h r / (b - a)) :=
    hlim.eventually (eventually_gt_nhds zero_lt_one)
  have hba : 0 < b - a := sub_pos.mpr hab
  filter_upwards [h1, eventually_ge_atTop D.threshold] with r hr hrd
  have hden : 0 < h r / (b - a) := div_pos (D.pos_above r hrd) hba
  rcases div_pos_iff.1 hr with ⟨hf, -⟩ | ⟨-, hneg⟩
  · exact hf
  · linarith

/-- **Lemma I.4.21, all conclusions together, for signed `f`**: the asymptotic
ratio, regular variation of index `b`, eventual non-vanishing and (derived)
eventual positivity, from hypotheses that nowhere assume a sign for `f`. -/
theorem lemma_I_4_21_signed {f f' : ℝ → ℝ} {h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (h r / (b - a))) atTop (𝓝 1) ∧
      RegularlyVaryingAtTop f b ∧ (∀ᶠ r in atTop, f r ≠ 0) ∧
        (∀ᶠ r in atTop, 0 < f r) :=
  ⟨lemma_I_4_21_tendsto_of_hasDerivAt D ha hab hderiv hasym,
   lemma_I_4_21_regularlyVarying_of_hasDerivAt D ha hab hderiv hasym,
   (lemma_I_4_21_regularlyVarying_of_hasDerivAt D ha hab hderiv hasym).1,
   lemma_I_4_21_eventually_pos_of_hasDerivAt D ha hab hderiv hasym⟩

/-! ## The paper's own form: `f` differentiable, `f'` its actual derivative

The source statement says only that `f` is differentiable and writes `f'(r)`
for the derivative.  The version below has no separate `f'`: it uses
`deriv f`, and no sign hypothesis on `f`. -/

/-- **Lemma I.4.21 in the paper's own quantifiers, for signed `f`.**

`a > 0`, `h` measurable regularly varying of index `b`, `f` differentiable,
`f'(r) ~ (a f(r) + h(r))/r` for the actual derivative `deriv f`, and `b > a`.
Then `f(r) ~ h(r)/(b-a)`, `f` is regularly varying of index `b`, and `f` is
eventually positive (derived). -/
theorem lemma_I_4_21_of_differentiableAt {f h : ℝ → ℝ} {b : ℝ} (D : RVPosData h b)
    {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hasym : Tendsto (fun r => deriv f r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (h r / (b - a))) atTop (𝓝 1) ∧
      RegularlyVaryingAtTop f b ∧ (∀ᶠ r in atTop, 0 < f r) := by
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (deriv f x) x :=
    fun x hx => (hdiff x hx).hasDerivAt
  obtain ⟨h1, h2, -, h4⟩ := lemma_I_4_21_signed D ha hab hderiv hasym
  exact ⟨h1, h2, h4⟩

/-! ## Consequence for the `a < b` branch of Lemma I.5.5

`Analysis.Lemma_I_5_5.lemma_I_5_5` assumes `0 < f` on `(0,∞)`.  In its
`a < b` branch it reaches the positive-`f` Lemma I.4.21 only, so that branch
does not need the hypothesis. -/

/-- **The `a < b` branch of Lemma I.5.5 without positivity of `f`**: `f` is
regularly varying of index `max a b = b`. -/
theorem lemma_I_5_5_branch_of_lt {f f' h : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h b)
    (hpos : ∀ x : ℝ, 0 < x → 0 < h x)
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1))
    (hab : a < b) :
    RegularlyVaryingAtTop f (max a b) := by
  have hhe : ∀ᶠ x in atTop, 0 < h x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hpos x hx
  let D : RVPosData h b := RVPosData.of hb hhm hhrv hhe
  have hfrv := lemma_I_4_21_regularlyVarying_of_hasDerivAt D ha hab hderiv hasym
  simpa [max_eq_right hab.le] using hfrv

/-! ## The two-term error form used by Lemma I.5.26

Lemma I.5.26 is stated for the two-term error `((a ± o(1)) f + (A ± o(1)) h)/r`,
formalized in `Analysis/Lemma_I_5_26.lean` as the hypothesis
`(r f' - a f)/h → A`.  The signed I.4.21 determines that same quantity in the
case `A = 1`, without the integrating-factor argument of I.5.26: from
`f' ~ (a f + h)/r` and `a < b` one gets `(r f' - a f)/h → 1`. -/

/-- **The two-term error of Lemma I.5.26 with `A = 1`**, derived from the
signed Lemma I.4.21.  Algebraically,
`(r f' - a f)/h = (f'/((a f + h)/r)) (a f/h + 1) - a f/h` wherever
`a f + h ≠ 0`, and both factors on the right have a limit: the first tends to
`1` by hypothesis, the second is built from `f/h → 1/(b-a)`. -/
theorem tendsto_two_term_error_of_driving_ode {f f' h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a : ℝ} (ha : 0 < a) (hab : a < b)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => (r * f' r - a * f r) / h r) atTop (𝓝 1) := by
  obtain ⟨r₀, δ, hr₀, hr₀1, hrD, hδm, hδ0, hδ1, hne, hode⟩ :=
    exists_shared_error_of_tendsto D ha hderiv hasym
  have hlim : Tendsto (fun r => f r / h r) atTop (𝓝 (1 / (b - a))) :=
    tendsto_div_of_driving_ode D ha hab hr₀ hr₀1 hrD
      (fun x hx => hderiv x (lt_of_lt_of_le hr₀ hx))
      hδm hδ0 hδ1 hode
  have heq : (fun r => (r * f' r - a * f r) / h r) =ᶠ[atTop]
      fun r => (f' r / ((a * f r + h r) / r)) * (a * (f r / h r) + 1) - a * (f r / h r) := by
    filter_upwards [D.rv.1, eventually_ge_atTop r₀, eventually_gt_atTop (0 : ℝ)]
      with r hhr hr₀r hr0
    have hne' : a * f r + h r ≠ 0 := hne r hr₀r
    field_simp [hne', hhr, ne_of_gt hr0]
  have hlim2 : Tendsto
      (fun r => (f' r / ((a * f r + h r) / r)) * (a * (f r / h r) + 1) - a * (f r / h r))
      atTop (𝓝 (1 * (a * (1 / (b - a)) + 1) - a * (1 / (b - a)))) :=
    ((hasym.mul ((hlim.const_mul a).add (tendsto_const_nhds (x := (1 : ℝ)))))).sub
      (hlim.const_mul a)
  have hval : 1 * (a * (1 / (b - a)) + 1) - a * (1 / (b - a)) = 1 := by ring
  rw [hval] at hlim2
  exact hlim2.congr' heq.symm

/-! ## Non-vacuity: the signed hypotheses hold for an `f` of both signs

`a = 1`, `b = 2`, `h(r) = r²`, `f(r) = r² - r` solves the asymptotic ODE
*exactly*, `f'(r) = 2r - 1 = (a f(r) + h(r))/r`, while `f` is negative on
`(0,1)`.  So the positive-`f` hypothesis of the existing lemma is genuinely
false here, and the signed lemma both applies and yields the eventual
positivity that the positive version assumed. -/

/-- The signed hypotheses of Lemma I.4.21 are satisfiable with a solution that
is not positive, so the generalization is strict rather than vacuous. -/
theorem signed_hypotheses_with_sign_changing_f :
    ∃ (f f' h : ℝ → ℝ) (a b : ℝ) (D : RVPosData h b),
      0 < a ∧ a < b ∧ (∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x) ∧
        Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1) ∧
        ¬ (∀ x : ℝ, 0 < x → 0 < f x) ∧
        Tendsto (fun r => f r / (h r / (b - a))) atTop (𝓝 1) ∧
        RegularlyVaryingAtTop f b ∧ (∀ᶠ r in atTop, 0 < f r) := by
  have hrv : RegularlyVaryingAtTop (fun x : ℝ => x ^ (2 : ℝ)) 2 :=
    regularlyVaryingAtTop_rpow 2
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < x ^ (2 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact Real.rpow_pos_of_pos hx 2
  let D : RVPosData (fun r : ℝ => r ^ (2 : ℝ)) 2 :=
    RVPosData.of (by norm_num) (by fun_prop) hrv hpos
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun r : ℝ => r ^ (2 : ℝ) - r) (2 * x - 1) x := by
    intro x hx
    have h1 : HasDerivAt (fun r : ℝ => r ^ (2 : ℝ)) (2 * x) x := by
      have h := Real.hasDerivAt_rpow_const (x := x) (p := (2 : ℝ)) (Or.inl hx.ne')
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] at h
      simpa using h
    have hid : HasDerivAt (fun r : ℝ => r) (1 : ℝ) x := hasDerivAt_id x
    have h2 := h1.sub hid
    have hfun : ((fun r : ℝ => r ^ (2 : ℝ)) - (fun r : ℝ => r)) =
        fun r : ℝ => r ^ (2 : ℝ) - r := rfl
    rw [hfun] at h2
    exact h2
  have hasym : Tendsto
      (fun r : ℝ => (2 * r - 1) / ((1 * (r ^ (2 : ℝ) - r) + r ^ (2 : ℝ)) / r))
      atTop (𝓝 1) := by
    have h : (fun r : ℝ => (2 * r - 1) / ((1 * (r ^ (2 : ℝ) - r) + r ^ (2 : ℝ)) / r))
        =ᶠ[atTop] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
      have hr0 : r ≠ 0 := by linarith
      have h2 : 1 * (r ^ (2 : ℝ) - r) + r ^ (2 : ℝ) = r * (2 * r - 1) := by
        rw [Real.rpow_two]; ring
      have h3 : 2 * r - 1 ≠ 0 := by linarith
      rw [h2, mul_div_cancel_left₀ _ hr0, div_self h3]
    exact tendsto_const_nhds.congr' h.symm
  have hnotpos : ¬ (∀ x : ℝ, 0 < x → 0 < (fun r : ℝ => r ^ (2 : ℝ) - r) x) := by
    intro h
    have h2 := h (1 / 2) (by norm_num)
    change 0 < (1 / 2 : ℝ) ^ (2 : ℝ) - 1 / 2 at h2
    have hval : ((1 / 2 : ℝ) ^ (2 : ℝ) - 1 / 2) = -(1 / 4) := by
      rw [Real.rpow_two]; norm_num
    rw [hval] at h2
    norm_num at h2
  exact ⟨fun r : ℝ => r ^ (2 : ℝ) - r, fun r : ℝ => 2 * r - 1,
    fun r : ℝ => r ^ (2 : ℝ), 1, 2, D, one_pos, by norm_num, hderiv, hasym, hnotpos,
    lemma_I_4_21_tendsto_of_hasDerivAt D one_pos (by norm_num) hderiv hasym,
    lemma_I_4_21_regularlyVarying_of_hasDerivAt D one_pos (by norm_num) hderiv hasym,
    lemma_I_4_21_eventually_pos_of_hasDerivAt D one_pos (by norm_num) hderiv hasym⟩

end PercLib.CriticalLRP.Analysis.I421Signed
