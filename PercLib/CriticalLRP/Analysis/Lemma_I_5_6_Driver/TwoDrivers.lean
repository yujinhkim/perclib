/- Integrated from independently rebuilt Ultramath work.
Production base 6b7eb1107b03297e4df33585eeac818682adb1d2.
Scratch source: repository-root .ultramath/smwwp7q3k/m2/.
-/

/-
# Lemma I.5.6 with the numerator carried by a second driver

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.5.6 (pp. 56-57).

The paper's statement has *one* error function: `δ₁` is logarithmically
integrable, and the inhomogeneous term carries a second factor
`(1 - δ₂,r) h(r)`.  The proof then reads

  "It suffices without loss of generality to consider the case `δ₂,r ≡ 0`,
   since `(1 - δ₂,r) h(r)` is regularly varying of the same index as `h` and
   shares the logarithmic integrability properties as `h` after multiplication
   by `r ^ (-a)`."

So the source's real hypothesis on the second error is a list of properties of
the *product* `H = (1 - δ₂) h`, not a condition on `δ₂` itself.  This file
proves the source statement for an arbitrary second driver `H` carrying exactly
those properties.  `Driver.lean` then derives them from the condition that the
second error is an error (`H / h → 1`) and recovers the committed two-error
statement.

Main results:

* `lemma_I_5_6_of_two_drivers` — Lemma I.5.6 for a positive, measurable,
  regularly varying second driver `H` of index `a` whose logarithmic
  integrability class matches that of `h` and whose divergent integral
  compares with that of `h`;
* `lemma_I_5_6_log_of_two_drivers` — the paper's "in particular" corollary.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_5_6_Driver.Help

/-! Removal of the second driver under an explicit integral comparison. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

@[expose] public section

open Filter Set MeasureTheory Real
open scoped Topology

namespace PercLib.CriticalLRP.Analysis.I56Driver

/-- **Lemma I.5.6 with the numerator carried by a second regularly varying
driver.**

`h` is the source's positive, measurable, regularly varying function of index
`a > 0`; `H` is the driver of the numerator, i.e. `(1 - δ₂) h` in the source's
notation, and is assumed to be the same kind of function, with the two extra
properties the source's reduction uses: it has the same logarithmic
integrability class as `h`, and its divergent integral `∫ H s / s ^ (a+1)`
compares with that of `h` whenever those integrals diverge.

Then the critical solution `f` of `f' = ((1 - δ₁) a f + H) / r` behaves as
asserted by Lemma I.5.6 relative to `h`: if `h r / r ^ a` fails to be
logarithmically integrable then `f r ∼ r ^ a ∫ h s / s ^ (a+1)`, and otherwise
`f r ∼ A r ^ a` for some `A > 0`. -/
theorem lemma_I_5_6_of_two_drivers {f f' h H δ : ℝ → ℝ} {a x₀ : ℝ} (ha : 0 < a)
    (hx₀ : 0 < x₀)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h a)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hHm : Measurable H) (hHrv : RegularlyVaryingAtTop H a)
    (hHpos : ∀ᶠ x in atTop, 0 < H x)
    (hlog : LogarithmicallyIntegrable (fun r => H r / r ^ a) ↔
      LogarithmicallyIntegrable (fun r => h r / r ^ a))
    (hUint₀ : ∀ x y : ℝ, x₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y)
    (hUHint₀ : ∀ x y : ℝ, x₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => H s / s ^ (a + 1)) volume x y)
    (hcmp : (¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
      Tendsto (fun r => (∫ s in x₀..r, H s / s ^ (a + 1)) /
        (∫ s in x₀..r, h s / s ^ (a + 1))) atTop (𝓝 1))
    (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ : IsLogErrorFunction δ)
    (hode : ∀ x, 0 < x → f' x = ((1 - δ x) * a * f x + H x) / x) :
    ∃ r₀ : ℝ, x₀ ≤ r₀ ∧ 0 < r₀ ∧
      (∀ x y : ℝ, r₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      ((¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1)))
          atTop (𝓝 1)) ∧
      ((LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A)) := by
  let D_H : RVPosData H a := RVPosData.of ha hHm hHrv hHpos
  let D_h : RVPosData h a := RVPosData.of ha hhm hhrv hpos
  let R : ℝ := max x₀ (max D_H.threshold D_h.threshold)
  have hx₀R : x₀ ≤ R := le_max_left _ _
  have hDHR : D_H.threshold ≤ R := (le_max_left _ _).trans (le_max_right x₀ _)
  have hDhR : D_h.threshold ≤ R := (le_max_right _ _).trans (le_max_right x₀ _)
  have hode' : ∀ x, 0 < x → f' x = (1 - δ x) * a * f x / x + H x / x := by
    intro x hx
    rw [hode x hx]
    field_simp
  obtain ⟨r₀, hrR, hr₀, _hU_H_int, hmain, hfinite⟩ :=
    lemma_I_5_6_reduced (R := R) ha hHm hHrv hHpos hfpos hderiv hδ hode'
  have hx₀r₀ : x₀ ≤ r₀ := hx₀R.trans hrR
  have hrDH : D_H.threshold ≤ r₀ := hDHR.trans hrR
  have hrDh : D_h.threshold ≤ r₀ := hDhR.trans hrR
  have hUint : ∀ x y : ℝ, r₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y :=
    fun x y hx hxy => hUint₀ x y (hx₀r₀.trans hx) hxy
  refine ⟨r₀, hx₀r₀, hr₀, hUint, ?_, ?_⟩
  · intro hnot
    have hnotH : ¬ LogarithmicallyIntegrable (fun r => H r / r ^ a) :=
      fun hc => hnot (hlog.mp hc)
    have hUpos : ∀ x, r₀ ≤ x → 0 < h x / x ^ (a + 1) := by
      intro x hx
      exact div_pos (D_h.pos_above x (hrDh.trans hx))
        (Real.rpow_pos_of_pos (hr₀.trans_le hx) (a + 1))
    have hum : Measurable (fun r => h r / r ^ a) := hhm.div (by fun_prop)
    have hnotU : ¬ IntegrableOn (fun s => h s / s ^ (a + 1)) (Ioi r₀) volume := by
      intro hUi
      apply hnot
      refine ⟨hum, r₀, hr₀, ?_⟩
      apply hUi.congr_fun _ measurableSet_Ioi
      intro s hs
      have hs0 : 0 < s := hr₀.trans hs
      have hsr₀ : r₀ ≤ s := hs.le
      have hupos : 0 < h s / s ^ a :=
        div_pos (D_h.pos_above s (hrDh.trans hsr₀)) (Real.rpow_pos_of_pos hs0 a)
      change h s / s ^ (a + 1) = |h s / s ^ a| / s
      rw [abs_of_pos hupos, Real.rpow_add hs0, Real.rpow_one]
      ring
    have hUtop : Tendsto (fun r => ∫ s in r₀..r, h s / s ^ (a + 1)) atTop atTop :=
      tendsto_intervalIntegral_atTop_of_not_integrableOn hUint (fun x hx => (hUpos x hx).le) hnotU
    have hshift := tendsto_intervalIntegral_div_shift (C := 1) one_pos hx₀r₀
      hUHint₀ hUint₀ hUtop (hcmp hnot)
    have hm := hmain hnotH
    have hmul := hm.mul hshift
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop r₀, hUtop.eventually (eventually_gt_atTop 0),
      hm.eventually (eventually_gt_nhds zero_lt_one)] with r hr hrI hgt
    have hr0 : 0 < r := hr₀.trans_le hr
    have hrh : 0 < ∫ s in r₀..r, h s / s ^ (a + 1) := hrI
    have hIH : ∫ s in r₀..r, H s / s ^ (a + 1) ≠ 0 := by
      intro hzero
      have hz : f r / (r ^ a * ∫ s in r₀..r, H s / s ^ (a + 1)) = 0 := by
        rw [hzero]
        simp
      rw [hz] at hgt
      exact lt_irrefl (0:ℝ) hgt
    change f r / (r ^ a * ∫ s in r₀..r, H s / s ^ (a + 1)) *
      ((∫ s in r₀..r, H s / s ^ (a + 1)) / (∫ s in r₀..r, h s / s ^ (a + 1))) =
      f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1))
    field_simp [hIH, hrh.ne', (Real.rpow_pos_of_pos hr0 a).ne']
  · intro hlogh
    exact hfinite (hlog.mpr hlogh)

/-- **The logarithmic corollary of Lemma I.5.6 for a second driver.** If
`h(r) ∼ A r ^ a` then the critical solution satisfies `f(r) ∼ A r ^ a log r`. -/
theorem lemma_I_5_6_log_of_two_drivers {f f' h H δ : ℝ → ℝ} {a A x₀ : ℝ} (ha : 0 < a)
    (hA : 0 < A) (hx₀ : 0 < x₀)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h a)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hHm : Measurable H) (hHrv : RegularlyVaryingAtTop H a)
    (hHpos : ∀ᶠ x in atTop, 0 < H x)
    (hlog : LogarithmicallyIntegrable (fun r => H r / r ^ a) ↔
      LogarithmicallyIntegrable (fun r => h r / r ^ a))
    (hUint₀ : ∀ x y : ℝ, x₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y)
    (hUHint₀ : ∀ x y : ℝ, x₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => H s / s ^ (a + 1)) volume x y)
    (hcmp : (¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
      Tendsto (fun r => (∫ s in x₀..r, H s / s ^ (a + 1)) /
        (∫ s in x₀..r, h s / s ^ (a + 1))) atTop (𝓝 1))
    (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ : IsLogErrorFunction δ)
    (hode : ∀ x, 0 < x → f' x = ((1 - δ x) * a * f x + H x) / x)
    (hhA : Tendsto (fun r => h r / (A * r ^ a)) atTop (𝓝 1)) :
    Tendsto (fun r => f r / (A * r ^ a * Real.log r)) atTop (𝓝 1) := by
  let u : ℝ → ℝ := fun r => h r / r ^ a
  have huA : Tendsto (fun r => u r / A) atTop (𝓝 1) := by
    apply hhA.congr'
    filter_upwards with r
    dsimp [u]
    ring
  have hulim : Tendsto u atTop (𝓝 A) := by
    have hm := huA.const_mul A
    rw [mul_one] at hm
    apply hm.congr'
    filter_upwards with r
    dsimp [u]
    field_simp [hA.ne']
  have hnot : ¬ LogarithmicallyIntegrable (fun r => h r / r ^ a) :=
    not_logarithmicallyIntegrable_of_tendsto_pos hA hulim
  obtain ⟨r₀, _, hr₀, hUint, hnon, _⟩ :=
    lemma_I_5_6_of_two_drivers ha hx₀ hhm hhrv hpos hHm hHrv hHpos hlog hUint₀ hUHint₀
      hcmp hfpos hderiv hδ hode
  exact log_corollary_of_divergent_branch (f := f) (h := h) (a := a) (A := A) (r₀ := r₀)
    hA hr₀ hUint (hnon hnot) hhA

end PercLib.CriticalLRP.Analysis.I56Driver

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_of_two_drivers
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_log_of_two_drivers
