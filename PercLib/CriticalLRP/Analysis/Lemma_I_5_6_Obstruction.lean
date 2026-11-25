/- Integrated from independently rebuilt Ultramath work.
Production base e6fb888fa60f4bb3d7fa5ab717b2d149345e3a7f.
Scratch source: repository-root .ultramath/smwwp7q3k/m2/Counter.lean.
-/

/-
# The source's `δ₂ ≡ 0` reduction is not implied by regular variation alone

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, proof of Lemma I.5.6 (p. 56):

  "It suffices without loss of generality to consider the case `δ₂,r ≡ 0`,
   since `(1 - δ₂,r) h(r)` is regularly varying of the same index as `h` and
   shares the logarithmic integrability properties as `h` after multiplication
   by `r ^ (-a)`."

This file records, as a compiled counterexample, that those two properties of
the product `H = (1 - δ₂) h` do not by themselves give the lemma's conclusion
*relative to `h`*: the divergent branch additionally needs the comparison
`∫ H s / s ^ (a+1) ~ ∫ h s / s ^ (a+1)`, which is exactly what `H / h → 1`
(that is, `δ₂ → 0`) supplies in `Driver.lean`.

Counterexample data (`a = 1`, `δ = 0`):

* `h r = r`, so `h r / r ^ a = 1` is not logarithmically integrable;
* `H r = 2 r - 3`, regularly varying of index `1`, eventually positive, and
  `H r / r → 2` also fails to be logarithmically integrable, so the two
  logarithmic integrability classes agree;
* `f r = 2 r log r + 3` is positive on `(0, ∞)` and solves
  `f' = ((1 - 0) * 1 * f + H) / r` with `f' r = 2 log r + 2`.

Then `f r / (r * ∫_{r₀}^{r} h s / s ^ 2 ds) → 2 ≠ 1` for every `r₀ > 0`, so the
divergent branch of the conclusion fails. Hence `hcmp` in
`lemma_I_5_6_of_two_drivers` (equivalently `H / h → 1` in
`lemma_I_5_6_of_driver`) is not removable, and the committed `δ₂ → 0`
hypothesis is genuinely used.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_5_6_Driver.Driver

/-! Why regular variation and log-integrability alone cannot discard the second driver. -/


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

@[expose] public section

open Filter Set MeasureTheory Real
open scoped Topology

namespace PercLib.CriticalLRP.Analysis.I56Driver

/-- `r ↦ r` is regularly varying of index `1`. -/
theorem regularlyVaryingAtTop_id_one : RegularlyVaryingAtTop (fun r : ℝ => r) 1 := by
  refine ⟨eventually_ne_atTop (0 : ℝ), fun l hl => ?_⟩
  rw [Real.rpow_one]
  have h : (fun x : ℝ => (l * x) / x) =ᶠ[atTop] (fun _ => l) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp
  exact tendsto_const_nhds.congr' h.symm

/-- `r ↦ 2 r - 3` is regularly varying of index `1`. -/
theorem regularlyVaryingAtTop_two_mul_sub : RegularlyVaryingAtTop (fun r : ℝ => 2 * r - 3) 1 := by
  refine ⟨?_, fun l hl => ?_⟩
  · filter_upwards [eventually_ne_atTop ((3 : ℝ) / 2)] with x hx h
    exact hx (by linarith)
  · rw [Real.rpow_one]
    have hlin : Tendsto (fun x : ℝ => 2 * x - 3) atTop atTop := by
      have h1 : Tendsto (fun x : ℝ => 2 * x) atTop atTop := tendsto_id.const_mul_atTop two_pos
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-3) h1
    have h0 : Tendsto (fun x : ℝ => (3 * l - 3) / (2 * x - 3)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlin
    have hsplit : (fun x : ℝ => (2 * (l * x) - 3) / (2 * x - 3)) =ᶠ[atTop]
        (fun x => l + (3 * l - 3) / (2 * x - 3)) := by
      filter_upwards [eventually_ne_atTop ((3 : ℝ) / 2)] with x hx
      have hx' : 2 * x - 3 ≠ 0 := by
        intro h
        exact hx (by linarith)
      field_simp
      ring
    have hstep : Tendsto (fun x : ℝ => l + (3 * l - 3) / (2 * x - 3)) atTop (𝓝 (l + 0)) :=
      tendsto_const_nhds.add h0
    rw [add_zero] at hstep
    exact hstep.congr' hsplit.symm

/-- The pointwise identity behind the counterexample's `h`. -/
theorem counter_h_fun : (fun s : ℝ => s / s ^ ((1 : ℝ) + 1)) = (fun s => 1 / s) := by
  funext s
  by_cases hs0 : s = 0
  · simp [hs0]
  · have h2 : ((1 : ℝ) + 1) = 2 := by norm_num
    rw [h2, Real.rpow_two]
    field_simp

/-- The pointwise identity behind the counterexample's `H`. -/
theorem counter_H_fun :
    (fun s : ℝ => (2 * s - 3) / s ^ ((1 : ℝ) + 1))
      = (fun s => 2 * (1 / s) - 3 * (1 / s ^ 2)) := by
  funext s
  by_cases hs0 : s = 0
  · simp [hs0]
  · have h2 : ((1 : ℝ) + 1) = 2 := by norm_num
    rw [h2, Real.rpow_two]
    field_simp

/-- The interval integral of the counterexample driver: `∫ s / s ^ 2 = log (r/r₀)`. -/
theorem integral_counter_driver {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r) :
    (∫ s in r₀..r, s / s ^ ((1 : ℝ) + 1)) = Real.log (r / r₀) := by
  have hzero : (0 : ℝ) ∉ uIcc r₀ r := by
    rw [uIcc_of_le hr]
    intro hmem
    linarith [hmem.1]
  rw [counter_h_fun, integral_one_div hzero]

/-- Interval integrability of the counterexample's `h` above a positive base point. -/
theorem intervalIntegrable_counter_h {x y x₀ : ℝ} (hx : x₀ ≤ x) (hx₀ : 0 < x₀)
    (hxy : x ≤ y) :
    IntervalIntegrable (fun s : ℝ => s / s ^ ((1 : ℝ) + 1)) volume x y := by
  rw [counter_h_fun]
  exact intervalIntegral.intervalIntegrable_one_div (f := fun s : ℝ => s) (fun s hs => by
    rw [uIcc_of_le hxy] at hs
    linarith [hs.1]) continuous_id.continuousOn

/-- Interval integrability of the counterexample's `H` above a positive base point. -/
theorem intervalIntegrable_counter_H {x y x₀ : ℝ} (hx : x₀ ≤ x) (hx₀ : 0 < x₀)
    (hxy : x ≤ y) :
    IntervalIntegrable (fun s : ℝ => (2 * s - 3) / s ^ ((1 : ℝ) + 1)) volume x y := by
  rw [counter_H_fun]
  have hone : IntervalIntegrable (fun s : ℝ => 1 / s) volume x y :=
    intervalIntegral.intervalIntegrable_one_div (f := fun s : ℝ => s) (fun s hs => by
      rw [uIcc_of_le hxy] at hs
      linarith [hs.1]) continuous_id.continuousOn
  have htwo : IntervalIntegrable (fun s : ℝ => 1 / s ^ 2) volume x y :=
    intervalIntegral.intervalIntegrable_one_div (f := fun s : ℝ => s ^ 2) (fun s hs => by
      rw [uIcc_of_le hxy] at hs
      have h1 : (0 : ℝ) < s := by linarith [hs.1]
      positivity) (continuous_id.pow 2).continuousOn
  exact (hone.const_mul 2).sub (htwo.const_mul 3)

/-- `f r = 2 r log r + 3` is positive on `(0, ∞)`. -/
theorem counter_f_pos : ∀ x : ℝ, 0 < x → 0 < 2 * x * Real.log x + 3 := by
  intro x hx
  have h1 : Real.log x ≥ 1 - 1 / x := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at h
    rw [one_div]
    linarith
  have hmul : (1 - 1 / x) * (2 * x) ≤ Real.log x * (2 * x) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have hesimp : (1 - 1 / x) * (2 * x) = 2 * x - 2 := by
    field_simp
  rw [hesimp, mul_comm (Real.log x) (2 * x)] at hmul
  linarith

/-- The ODE of the counterexample. -/
theorem counter_ode (x : ℝ) (hx : 0 < x) :
    2 * Real.log x + 2 = ((1 - 0) * 1 * (2 * x * Real.log x + 3) + (2 * x - 3)) / x := by
  field_simp
  ring

/-- Differentiability of the counterexample solution. -/
theorem counter_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun r : ℝ => 2 * r * Real.log r + 3) (2 * Real.log x + 2) x := by
  have h1 : HasDerivAt (fun r : ℝ => r * Real.log r) (Real.log x + 1) x :=
    Real.hasDerivAt_mul_log hx.ne'
  have h2 := (h1.const_mul (2 : ℝ)).add_const (3 : ℝ)
  have hval : 2 * (Real.log x + 1) = 2 * Real.log x + 2 := by ring
  rw [hval] at h2
  have heq : (fun r : ℝ => 2 * (r * Real.log r) + 3) = (fun r => 2 * r * Real.log r + 3) := by
    funext r
    ring
  rw [heq] at h2
  exact h2

/-- The `H r / r → 2` limit of the counterexample driver. -/
theorem tendsto_counter_driver_div :
    Tendsto (fun r : ℝ => (2 * r - 3) / r ^ (1 : ℝ)) atTop (𝓝 2) := by
  have h : (fun r : ℝ => (2 * r - 3) / r ^ (1 : ℝ)) =ᶠ[atTop] (fun r => 2 - 3 / r) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
    rw [Real.rpow_one]
    field_simp
  have hlim : Tendsto (fun r : ℝ => 2 - 3 / r) atTop (𝓝 (2 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
  rw [sub_zero] at hlim
  exact hlim.congr' h.symm

/-- The `h r / r → 1` limit of the counterexample. -/
theorem tendsto_counter_h_div : Tendsto (fun r : ℝ => r / r ^ (1 : ℝ)) atTop (𝓝 1) := by
  have h : (fun r : ℝ => r / r ^ (1 : ℝ)) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with r hr
    rw [Real.rpow_one]
    field_simp
  exact tendsto_const_nhds.congr' h.symm

/-- The ratio of the counterexample solution to the source's normalisation tends
to `2`, for every base point `r₀ > 0`. -/
theorem tendsto_counter_ratio {r₀ : ℝ} (hr₀ : 0 < r₀) :
    Tendsto (fun r => (2 * r * Real.log r + 3) /
      (r ^ (1 : ℝ) * ∫ s in r₀..r, s / s ^ ((1 : ℝ) + 1))) atTop (𝓝 2) := by
  have hident : (fun r => (2 * r * Real.log r + 3) /
        (r ^ (1 : ℝ) * ∫ s in r₀..r, s / s ^ ((1 : ℝ) + 1)))
      =ᶠ[atTop] (fun r => 2 + (2 * Real.log r₀ + 3 / r) / (Real.log r - Real.log r₀)) := by
    filter_upwards [eventually_gt_atTop (max r₀ 1)] with r hr
    have hr₀r : r₀ < r := lt_of_le_of_lt (le_max_left _ _) hr
    have hr0 : 0 < r := hr₀.trans hr₀r
    rw [integral_counter_driver hr₀ hr₀r.le, Real.rpow_one,
      Real.log_div hr0.ne' hr₀.ne']
    have hc : Real.log r - Real.log r₀ ≠ 0 := by
      have hlt := Real.log_lt_log hr₀ hr₀r
      linarith
    field_simp [hr0.ne', hc]
    ring
  have hlim : Tendsto (fun r => 2 + (2 * Real.log r₀ + 3 / r) /
      (Real.log r - Real.log r₀)) atTop (𝓝 2) := by
    have hden : Tendsto (fun r : ℝ => Real.log r - Real.log r₀) atTop atTop := by
      have h := tendsto_atTop_add_const_right atTop (-Real.log r₀) Real.tendsto_log_atTop
      simpa [sub_eq_add_neg] using h
    have hnum : Tendsto (fun r : ℝ => 2 * Real.log r₀ + 3 / r) atTop
        (𝓝 (2 * Real.log r₀ + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    have h0 : Tendsto (fun r : ℝ => (2 * Real.log r₀ + 3 / r) /
        (Real.log r - Real.log r₀)) atTop (𝓝 0) :=
      hnum.div_atTop hden
    have hstep : Tendsto (fun r : ℝ => 2 + (2 * Real.log r₀ + 3 / r) /
        (Real.log r - Real.log r₀)) atTop (𝓝 (2 + 0)) :=
      tendsto_const_nhds.add h0
    rw [add_zero] at hstep
    exact hstep
  exact hlim.congr' hident.symm

/-- **Deleting only the divergent-integral comparison makes the two-driver
interface false.**

The data below satisfy *every* hypothesis of
`lemma_I_5_6_of_two_drivers` except `hcmp` (with `x₀ = 1`), the driver is in the
divergent case (`¬LogInt (h/r^a)`), and the divergent branch of the source
conclusion fails for every base point `r₀ > 0`.

In particular the two properties the paper invokes to justify `δ₂ ≡ 0` —
regular variation of the same index and coincidence of the logarithmic
integrability classes — do not suffice: here `H / h → 2`, not `1`. -/
theorem lemma_I_5_6_relaxed_false :
    ∃ (f f' h H δ : ℝ → ℝ) (a x₀ : ℝ), 0 < a ∧ 0 < x₀ ∧ Measurable h ∧
      RegularlyVaryingAtTop h a ∧ (∀ᶠ x in atTop, 0 < h x) ∧
      Measurable H ∧ RegularlyVaryingAtTop H a ∧ (∀ᶠ x in atTop, 0 < H x) ∧
      (LogarithmicallyIntegrable (fun r => H r / r ^ a) ↔
        LogarithmicallyIntegrable (fun r => h r / r ^ a)) ∧
      (∀ x y : ℝ, x₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      (∀ x y : ℝ, x₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => H s / s ^ (a + 1)) volume x y) ∧
      (∀ x, 0 < x → 0 < f x) ∧ (∀ x, 0 < x → HasDerivAt f (f' x) x) ∧
      IsLogErrorFunction δ ∧
      (∀ x, 0 < x → f' x = ((1 - δ x) * a * f x + H x) / x) ∧
      ¬ LogarithmicallyIntegrable (fun r => h r / r ^ a) ∧
      ∀ r₀ : ℝ, 0 < r₀ → ¬ Tendsto (fun r => f r / (r ^ a *
        ∫ s in r₀..r, h s / s ^ (a + 1))) atTop (𝓝 1) := by
  have hneH : ¬ LogarithmicallyIntegrable (fun r : ℝ => (2 * r - 3) / r ^ (1 : ℝ)) :=
    not_logarithmicallyIntegrable_of_tendsto_pos two_pos tendsto_counter_driver_div
  have hneh : ¬ LogarithmicallyIntegrable (fun r : ℝ => r / r ^ (1 : ℝ)) :=
    not_logarithmicallyIntegrable_of_tendsto_pos one_pos tendsto_counter_h_div
  have hHpos : ∀ᶠ x : ℝ in atTop, 0 < 2 * x - 3 := by
    filter_upwards [eventually_gt_atTop ((3 : ℝ) / 2)] with r hr
    linarith
  have hfpos : ∀ x : ℝ, 0 < x → 0 < 2 * x * Real.log x + 3 := counter_f_pos
  refine ⟨fun r => 2 * r * Real.log r + 3, fun r => 2 * Real.log r + 2, fun r => r,
    fun r => 2 * r - 3, fun _ => 0, 1, 1, one_pos, one_pos, measurable_id,
    regularlyVaryingAtTop_id_one, eventually_gt_atTop (0 : ℝ),
    (measurable_const.mul measurable_id).sub measurable_const,
    regularlyVaryingAtTop_two_mul_sub, hHpos,
    ⟨fun hc => absurd hc hneH, fun hc => absurd hc hneh⟩, ?_, ?_,
    hfpos, fun x hx => counter_hasDerivAt x hx, ?_, fun x hx => counter_ode x hx,
    hneh, ?_⟩
  · intro x y hx _
    exact intervalIntegrable_counter_h hx one_pos ‹x ≤ y›
  · intro x y hx _
    exact intervalIntegrable_counter_H hx one_pos ‹x ≤ y›
  · refine ⟨⟨measurable_const, 1, one_pos, ?_⟩, tendsto_const_nhds⟩
    have hzero : (fun r : ℝ => |(0 : ℝ)| / r) = (fun _ => (0 : ℝ)) := by
      funext r
      simp
    rw [hzero]
    exact integrableOn_zero
  · intro r₀ hr₀ h1
    have h2 := tendsto_counter_ratio (r₀ := r₀) hr₀
    have h12 : (1 : ℝ) = 2 := tendsto_nhds_unique h1 h2
    norm_num at h12

end PercLib.CriticalLRP.Analysis.I56Driver

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_relaxed_false
