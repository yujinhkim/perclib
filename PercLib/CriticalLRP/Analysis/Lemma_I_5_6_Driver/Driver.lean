/- Integrated from independently rebuilt Ultramath work.
Production base 6b7eb1107b03297e4df33585eeac818682adb1d2.
Scratch source: repository-root .ultramath/smwwp7q3k/m2/.
-/

/-
# Lemma I.5.6 from a second driver that is asymptotically `h`

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.5.6 (pp. 56-57).

`TwoDrivers.lean` proves the source statement for an arbitrary second driver
`H` satisfying the hypotheses the source's reduction needs.  This file derives
those hypotheses from the single condition that the second error is an error,
`H / h → 1` — which is what `δ₂ → 0` means for `H = (1 - δ₂) h` — and then
recovers the committed two-error statement of `Analysis/Lemma_I_5_6.lean` from
the new interface, so that the measurable-and-convergent `δ₂` hypotheses there
are *removed* rather than merely restated.

Main results:

* `lemma_I_5_6_of_driver` — Lemma I.5.6 under `H / h → 1`, with no `δ₂` at all;
* `lemma_I_5_6_log_of_driver` — its logarithmic corollary;
* `lemma_I_5_6_of_errors_of_driver` — the committed two-error statement
  (`Measurable δ₂`, `δ₂ → 0`) as a consequence of the driver interface;
* `lemma_I_5_6_log_of_errors_of_driver` — its logarithmic corollary.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_5_6_Driver.TwoDrivers

/-! The second-driver comparison from a unit driver ratio. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

@[expose] public section

open Filter Set MeasureTheory Real
open scoped Topology

namespace PercLib.CriticalLRP.Analysis.I56Driver

/-- **Lemma I.5.6 with the second error eliminated.**

The numerator driver `H` is asymptotically `h` (`H / h → 1`); in the source's
notation `H = (1 - δ₂) h`, so this is exactly the assertion that the second
error vanishes.  No measurability or convergence of `δ₂` is assumed, because
`δ₂` does not occur: the hypotheses are on `H` itself.  The conclusion is the
source statement relative to `h`. -/
theorem lemma_I_5_6_of_driver {f f' h H δ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h a)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hHm : Measurable H) (hratio : Tendsto (fun r => H r / h r) atTop (𝓝 1))
    (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ : IsLogErrorFunction δ)
    (hode : ∀ x, 0 < x → f' x = ((1 - δ x) * a * f x + H x) / x) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ x y : ℝ, r₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      ((¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1)))
          atTop (𝓝 1)) ∧
      ((LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A)) := by
  have hHrv : RegularlyVaryingAtTop H a := RegularlyVaryingAtTop.of_tendsto_div hhrv hratio
  have hHpos : ∀ᶠ x in atTop, 0 < H x := by
    filter_upwards [hpos, hratio.eventually (eventually_gt_nhds zero_lt_one)] with r hr hq
    have he : H r = (H r / h r) * h r := (div_mul_cancel₀ (H r) hr.ne').symm
    rw [he]
    exact mul_pos hq hr
  let D_H : RVPosData H a := RVPosData.of ha hHm hHrv hHpos
  let D_h : RVPosData h a := RVPosData.of ha hhm hhrv hpos
  let x₀ : ℝ := max D_h.threshold D_H.threshold
  have hx₀1 : 1 ≤ x₀ := D_h.one_le_threshold.trans (le_max_left _ _)
  have hx₀ : 0 < x₀ := lt_of_lt_of_le one_pos hx₀1
  have hth_h : D_h.threshold ≤ x₀ := le_max_left _ _
  have hth_H : D_H.threshold ≤ x₀ := le_max_right _ _
  have hratio_meas : Measurable (fun r => H r / h r) := hHm.div hhm
  have hlogH : LogarithmicallyIntegrable (fun r => h r / r ^ a) →
      LogarithmicallyIntegrable (fun r => H r / r ^ a) := by
    intro hu
    have hm := logarithmicallyIntegrable_mul_of_tendsto_pos one_pos hratio hu hratio_meas
    refine hm.congr_of_eventuallyEq ?_ (hHm.div (by fun_prop))
    filter_upwards [hpos, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    field_simp [hr.ne', (Real.rpow_pos_of_pos hr0 a).ne']
  have hlogh : LogarithmicallyIntegrable (fun r => H r / r ^ a) →
      LogarithmicallyIntegrable (fun r => h r / r ^ a) := by
    intro hu
    have hm := logarithmicallyIntegrable_div_of_tendsto_pos one_pos hratio hu hratio_meas
    refine hm.congr_of_eventuallyEq ?_ (hhm.div (by fun_prop))
    filter_upwards [hpos, hHpos, eventually_gt_atTop (0 : ℝ)] with r hr hrH hr0
    field_simp [hr.ne', hrH.ne', (Real.rpow_pos_of_pos hr0 a).ne']
  have hlog : LogarithmicallyIntegrable (fun r => H r / r ^ a) ↔
      LogarithmicallyIntegrable (fun r => h r / r ^ a) := ⟨hlogh, hlogH⟩
  have hUint₀ : ∀ x y : ℝ, x₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y :=
    fun x y hx hxy => intervalIntegrable_div_rpow_succ D_h (hth_h.trans hx) hxy
  have hUHint₀ : ∀ x y : ℝ, x₀ ≤ x → x ≤ y →
      IntervalIntegrable (fun s => H s / s ^ (a + 1)) volume x y :=
    fun x y hx hxy => intervalIntegrable_div_rpow_succ D_H (hth_H.trans hx) hxy
  have hcmp : (¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
      Tendsto (fun r => (∫ s in x₀..r, H s / s ^ (a + 1)) /
        (∫ s in x₀..r, h s / s ^ (a + 1))) atTop (𝓝 1) := by
    intro hnot
    have hUpos : ∀ x, x₀ ≤ x → 0 < h x / x ^ (a + 1) := by
      intro x hx
      exact div_pos (D_h.pos_above x (hth_h.trans hx))
        (Real.rpow_pos_of_pos (hx₀.trans_le hx) (a + 1))
    have hnotU : ¬ IntegrableOn (fun s => h s / s ^ (a + 1)) (Ioi x₀) volume := by
      intro hUi
      apply hnot
      refine ⟨hhm.div (by fun_prop), x₀, hx₀, ?_⟩
      apply hUi.congr_fun _ measurableSet_Ioi
      intro s hs
      have hs0 : 0 < s := hx₀.trans hs
      have hupos : 0 < h s / s ^ a :=
        div_pos (D_h.pos_above s (hth_h.trans hs.le)) (Real.rpow_pos_of_pos hs0 a)
      change h s / s ^ (a + 1) = |h s / s ^ a| / s
      rw [abs_of_pos hupos, Real.rpow_add hs0, Real.rpow_one]
      ring
    have hUtop : Tendsto (fun r => ∫ s in x₀..r, h s / s ^ (a + 1)) atTop atTop :=
      tendsto_intervalIntegral_atTop_of_not_integrableOn hUint₀
        (fun x hx => (hUpos x hx).le) hnotU
    have hUratio : Tendsto (fun s => (H s / s ^ (a + 1)) / (h s / s ^ (a + 1)))
        atTop (𝓝 1) := by
      apply hratio.congr'
      filter_upwards [eventually_ge_atTop x₀, hpos] with s hs hspos
      have hs0 : 0 < s := hx₀.trans_le hs
      field_simp [hspos.ne', (Real.rpow_pos_of_pos hs0 (a + 1)).ne']
    exact tendsto_intervalIntegral_div_of_tendsto_ratio hUpos hUratio hUHint₀ hUint₀ hUtop
  obtain ⟨r₀, _, hr₀, hUint, hnon, hfin⟩ :=
    lemma_I_5_6_of_two_drivers ha hx₀ hhm hhrv hpos hHm hHrv hHpos hlog hUint₀ hUHint₀
      hcmp hfpos hderiv hδ hode
  exact ⟨r₀, hr₀, hUint, hnon, hfin⟩

/-- **The logarithmic corollary of Lemma I.5.6 with the second error
eliminated.** If `h(r) ∼ A r ^ a` then `f(r) ∼ A r ^ a log r`. -/
theorem lemma_I_5_6_log_of_driver {f f' h H δ : ℝ → ℝ} {a A : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h a)
    (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hHm : Measurable H) (hratio : Tendsto (fun r => H r / h r) atTop (𝓝 1))
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
  obtain ⟨r₀, hr₀, hUint, hnon, _⟩ :=
    lemma_I_5_6_of_driver ha hhm hhrv hpos hHm hratio hfpos hderiv hδ hode
  exact log_corollary_of_divergent_branch (f := f) (h := h) (a := a) (A := A) (r₀ := r₀)
    hA hr₀ hUint (hnon hnot) hhA

/-- **The committed two-error statement of Lemma I.5.6, derived from the driver
interface.** The hypotheses on `δ₂` are exactly the committed ones (measurable
and tending to zero); they enter only by producing a driver `H = (1 - δ₂) h`
with `H / h → 1`. -/
theorem lemma_I_5_6_of_errors_of_driver {f f' h δ₁ δ₂ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hhm : Measurable h) (hhrv : RegularlyVaryingAtTop h a)
    (hpos : ∀ᶠ x in atTop, 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂m : Measurable δ₂)
    (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ x, 0 < x →
      f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ x y : ℝ, r₀ ≤ x → x ≤ y →
        IntervalIntegrable (fun s => h s / s ^ (a + 1)) volume x y) ∧
      ((¬ LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        Tendsto (fun r => f r / (r ^ a * ∫ s in r₀..r, h s / s ^ (a + 1)))
          atTop (𝓝 1)) ∧
      ((LogarithmicallyIntegrable (fun r => h r / r ^ a)) →
        ∃ A : ℝ, 0 < A ∧ Tendsto (fun r => f r / r ^ a) atTop (𝓝 A)) := by
  have hHm : Measurable (fun r => (1 - δ₂ r) * h r) := (measurable_const.sub hδ₂m).mul hhm
  have hfac : Tendsto (fun r => 1 - δ₂ r) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hδ₂0
  have hratio : Tendsto (fun r => (1 - δ₂ r) * h r / h r) atTop (𝓝 1) := by
    apply hfac.congr'
    filter_upwards [hpos] with r hr
    field_simp [hr.ne']
  exact lemma_I_5_6_of_driver ha hhm hhrv hpos hHm hratio hfpos hderiv hδ₁ hode

/-- **The committed logarithmic corollary of Lemma I.5.6, derived from the
driver interface.** -/
theorem lemma_I_5_6_log_of_errors_of_driver {f f' h δ₁ δ₂ : ℝ → ℝ} {a A : ℝ}
    (ha : 0 < a) (hA : 0 < A) (hhm : Measurable h)
    (hhrv : RegularlyVaryingAtTop h a) (hpos : ∀ᶠ x in atTop, 0 < h x)
    (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hδ₁ : IsLogErrorFunction δ₁) (hδ₂m : Measurable δ₂)
    (hδ₂0 : Tendsto δ₂ atTop (𝓝 0))
    (hode : ∀ x, 0 < x →
      f' x = ((1 - δ₁ x) * a * f x + (1 - δ₂ x) * h x) / x)
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
  obtain ⟨r₀, hr₀, hUint, hnon, _⟩ :=
    lemma_I_5_6_of_errors_of_driver ha hhm hhrv hpos hfpos hderiv hδ₁ hδ₂m hδ₂0 hode
  exact log_corollary_of_divergent_branch (f := f) (h := h) (a := a) (A := A) (r₀ := r₀)
    hA hr₀ hUint (hnon hnot) hhA

end PercLib.CriticalLRP.Analysis.I56Driver

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_of_driver
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_log_of_driver
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_of_errors_of_driver
#print axioms PercLib.CriticalLRP.Analysis.I56Driver.lemma_I_5_6_log_of_errors_of_driver
