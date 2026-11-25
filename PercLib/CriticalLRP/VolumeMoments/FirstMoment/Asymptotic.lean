/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Member m5, swarm smwg5u3az — direction E (HD first-moment asymptotics).

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.4.1, Proposition I.4.2 (first moment).

Content:
* `tendsto_rpow_mul_integral_Ioi`: if `h → 0` then `r^a ∫_r^∞ h(s)s^{-a-1}ds → 0`.
* `first_moment_lower_bound`: **Corollary I.4.8** (`f r ≥ (α/A) r^α` when the
  error `h ≥ 0`), valid with no dimensional hypothesis.
* `one_add_error_eq`: the exact identity `1 + H_r = (1 − α r^α ∫_r^∞ h s s^{−α−1} ds)^{−1}`
  for `H_r = (A/α) r^{−α} f r − 1`, obtained from formula (I.4.7)
  (`PercLib.CriticalLRP.Analysis.lemma_I_4_5_three`).
* `first_moment_asymptotic`: `h → 0` implies `f r / ((α/A) r^α) → 1`,
  i.e. `E_{β,r}|K| ∼ (α/β) r^α` — the conclusion of Proposition I.4.2.
* `first_moment_error_logIntegrable`: **Lemma I.4.13 (first clause)** applied to
  this error: if `h` is a logarithmically integrable error function then so is
  `H_r`, by `integrableOn_hardyUpper`.

Hypotheses are those of Lemma I.4.5(3): `f` differentiable on `[r₀,∞)`, positive
there, `f → ∞`, `f' = A(1−h) r^{−α−1} f²` with `h` measurable and bounded.  No
continuity of `h` or of `f'`.  Measurability of `H` is an explicit hypothesis
(in the application it comes from measurability of `r ↦ E_{β,r}|K|`).
-/
module

public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.LogIntegrability

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.VolumeMoments.FirstMoment

/-! ### A tail-integral limit -/

/-- If `h → 0` then `r^a ∫_r^∞ h(s) s^{-a-1} ds → 0`. -/
theorem tendsto_rpow_mul_integral_Ioi {h : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hm : Measurable h) (h0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun r => r ^ a * ∫ s in Ioi r, h s * s ^ (-a - 1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hεa : 0 < ε * a / 2 := by positivity
  obtain ⟨R, hR⟩ := (Metric.tendsto_atTop.1 h0) (ε * a / 2) hεa
  refine ⟨max R 1, fun r hr => ?_⟩
  have hrR : R ≤ r := le_trans (le_max_left _ _) hr
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  rw [Real.dist_eq, sub_zero, abs_mul]
  have hpowpos : 0 < r ^ a := Real.rpow_pos_of_pos hr0 a
  rw [abs_of_pos hpowpos]
  have hbase : IntegrableOn (fun s : ℝ => s ^ (-a - 1)) (Ioi r) volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hr0
  have hdom : IntegrableOn (fun s : ℝ => (ε * a / 2) * s ^ (-a - 1)) (Ioi r) volume :=
    hbase.const_mul _
  have hle_ae : ∀ᵐ s ∂(volume.restrict (Ioi r)), |h s * s ^ (-a - 1)|
      ≤ (ε * a / 2) * s ^ (-a - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hr0 hs
    have hsR : R ≤ s := le_trans hrR hs.le
    have hle : |h s| ≤ ε * a / 2 := by
      have hlt := hR s hsR
      rw [Real.dist_eq, sub_zero] at hlt
      exact le_of_lt hlt
    have hpow : 0 ≤ s ^ (-a - 1) := Real.rpow_nonneg hs0.le _
    rw [abs_mul, abs_of_nonneg hpow]
    exact mul_le_mul_of_nonneg_right hle hpow
  have hleft : IntegrableOn (fun s : ℝ => |h s * s ^ (-a - 1)|) (Ioi r) volume := by
    refine Integrable.mono hdom
      ((hm.mul (by fun_prop : Measurable fun s : ℝ => s ^ (-a - 1))).abs.aestronglyMeasurable) ?_
    filter_upwards [hle_ae, ae_restrict_mem measurableSet_Ioi] with s hs hmem
    have hs0 : 0 < s := lt_trans hr0 hmem
    have hpos : 0 ≤ ε * a / 2 * s ^ (-a - 1) := by positivity
    have hnn : 0 ≤ |h s * s ^ (-a - 1)| := abs_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_nonneg hpos]
    exact hs
  have hbound : |∫ s in Ioi r, h s * s ^ (-a - 1)|
      ≤ (ε * a / 2) * (r ^ (-a) / a) := by
    have hb1 : |∫ s in Ioi r, h s * s ^ (-a - 1)|
        ≤ ∫ s in Ioi r, |h s * s ^ (-a - 1)| := abs_integral_le_integral_abs
    have hb2 : ∫ s in Ioi r, |h s * s ^ (-a - 1)|
        ≤ ∫ s in Ioi r, (ε * a / 2) * s ^ (-a - 1) :=
      integral_mono_ae hleft hdom hle_ae
    have hval : ∫ s in Ioi r, (ε * a / 2) * s ^ (-a - 1)
        = (ε * a / 2) * (r ^ (-a) / a) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (a := -a - 1) (by linarith) hr0]
      have h1 : -a - 1 + 1 = -a := by ring
      rw [h1]
      field_simp
    exact le_trans hb1 (le_trans hb2 (le_of_eq hval))
  have hfin : r ^ a * ((ε * a / 2) * (r ^ (-a) / a)) = ε / 2 := by
    have hrne : r ≠ 0 := ne_of_gt hr0
    have hane : a ≠ 0 := ne_of_gt ha
    have hrr : r ^ a * r ^ (-a) = 1 := by
      rw [← Real.rpow_add hr0]
      norm_num
    field_simp
    linarith [hrr]
  calc r ^ a * |∫ s in Ioi r, h s * s ^ (-a - 1)|
      ≤ r ^ a * ((ε * a / 2) * (r ^ (-a) / a)) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt hpowpos)
    _ = ε / 2 := hfin
    _ < ε := by linarith

section ExactSolution

variable {f f' h : ℝ → ℝ} {A α r₀ C : ℝ}

/-- **Corollary I.4.8** (paper p. 36): if the error `h` is nonnegative then
`f r ≥ (α/A) r^α`, with no dimensional hypothesis. -/
theorem first_moment_lower_bound
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (hnn : ∀ t, r₀ ≤ t → 0 ≤ h t) :
    ∀ r, r₀ ≤ r → α / A * r ^ α ≤ f r := by
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hform := PercLib.CriticalLRP.Analysis.lemma_I_4_5_three hA hα hr₀ hderiv hpos hinf
    hode hmeas hC r hr
  set I : ℝ := ∫ s in Ioi r, h s * s ^ (-α - 1) with hI
  have hInn : 0 ≤ I := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := lt_trans hr0 hs
    exact mul_nonneg (hnn s (le_trans hr hs.le)) (Real.rpow_nonneg hs0.le _)
  have hrαpos : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
  have hf0 : 0 < α / A * r ^ α := by positivity
  have hden : 0 < 1 - α * r ^ α * I := by
    have h1 : 0 < (α / A) * r ^ α / (1 - α * r ^ α * I) := by
      rw [← hform]
      exact hpos r hr
    rcases (div_pos_iff).1 h1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · linarith
  have hle1 : 1 - α * r ^ α * I ≤ 1 := by
    have h2 : 0 ≤ α * r ^ α * I := by positivity
    linarith
  rw [hform, le_div_iff₀ hden]
  nlinarith [hf0]

/-- The error `H_r = (A/α) r^{-α} f r − 1` in closed form: on `[r₀,∞)`,
`1 + H_r = (1 − α r^α ∫_r^∞ h s s^{-α-1} ds)^{-1}`. -/
theorem one_add_error_eq
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C) :
    ∀ r, r₀ ≤ r →
      1 + (A / α * r ^ (-α) * f r - 1)
        = (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))⁻¹ := by
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hform := PercLib.CriticalLRP.Analysis.lemma_I_4_5_three hA hα hr₀ hderiv hpos hinf
    hode hmeas hC r hr
  set I : ℝ := ∫ s in Ioi r, h s * s ^ (-α - 1) with hI
  have hrr : r ^ (-α) * r ^ α = 1 := by
    rw [← Real.rpow_add hr0]
    norm_num
  have hAne : A ≠ 0 := ne_of_gt hA
  have hαne : α ≠ 0 := ne_of_gt hα
  have hdenne : 1 - α * r ^ α * I ≠ 0 := by
    intro hc
    rw [hc] at hform
    simp at hform
    linarith [hpos r hr]
  rw [hform]
  have h1 : A / α * r ^ (-α) * (α / A * r ^ α / (1 - α * r ^ α * I))
      = (r ^ (-α) * r ^ α) * (1 - α * r ^ α * I)⁻¹ := by
    field_simp
  rw [h1, hrr, one_mul]
  ring

/-- **Proposition I.4.2, analytic core**: `Ē_{1,r} → 0` implies
`E_{β,r}|K| ~ (α/A) r^α`, i.e. `f r / ((α/A) r^α) → 1`. -/
theorem first_moment_asymptotic
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun r => f r / (α / A * r ^ α)) atTop (𝓝 1) := by
  have hw : Tendsto (fun r : ℝ => r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) atTop (𝓝 0) :=
    tendsto_rpow_mul_integral_Ioi hα hmeas h0
  have hden : Tendsto (fun r : ℝ => 1 - α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun r : ℝ => α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)))
        atTop (𝓝 0) := by simpa using hw.const_mul α
    simpa using tendsto_const_nhds.sub h1
  have hinv : Tendsto
      (fun r : ℝ => (1 - α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)))⁻¹) atTop (𝓝 1) := by
    simpa using hden.inv₀ (by norm_num : (1:ℝ) ≠ 0)
  refine hinv.congr' ?_
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hform := PercLib.CriticalLRP.Analysis.lemma_I_4_5_three hA hα hr₀ hderiv hpos hinf
    hode hmeas hC r hr
  set I : ℝ := ∫ s in Ioi r, h s * s ^ (-α - 1) with hI
  have hcoe : 0 < α / A * r ^ α := by
    have h2 : 0 < r ^ α := Real.rpow_pos_of_pos hr0 α
    positivity
  have hcoene : α / A * r ^ α ≠ 0 := ne_of_gt hcoe
  have hdenne : 1 - α * r ^ α * I ≠ 0 := by
    intro hc
    rw [hc] at hform
    simp at hform
    linarith [hpos r hr]
  rw [hform]
  field_simp

/-- **Lemma I.4.13 (first clause) applied to the error of the first-moment ODE**:
if the error profile is a logarithmically integrable error function then so is
`H_r = (A/α) r^{-α} f r − 1`. -/
theorem first_moment_error_logIntegrable
    (hA : 0 < A) (hα : 0 < α) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < f t)
    (hinf : Tendsto f atTop atTop)
    (hode : ∀ t, r₀ ≤ t → f' t = A * (1 - h t) * t ^ (-α - 1) * (f t) ^ 2)
    (hmeas : Measurable h) (hC : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (hlint : PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable h)
    (hHmeas : Measurable (fun r => A / α * r ^ (-α) * f r - 1)) :
    PercLib.CriticalLRP.Analysis.LogarithmicallyIntegrable
      (fun r => A / α * r ^ (-α) * f r - 1) := by
  obtain ⟨-, r₁, hr₁, hint⟩ := hlint
  have hmaj := integrableOn_hardyUpper hα hr₁ hmeas hint
  have hw : Tendsto (fun r : ℝ => r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) atTop (𝓝 0) :=
    tendsto_rpow_mul_integral_Ioi hα hmeas h0
  have hsmall : ∀ᶠ r : ℝ in atTop, |α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))| ≤ 1 / 2 := by
    have h1 : Tendsto (fun r : ℝ => α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)))
        atTop (𝓝 0) := by simpa using hw.const_mul α
    have h2 : Tendsto (fun r : ℝ => |α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1))|)
        atTop (𝓝 0) := by simpa using h1.abs
    exact h2.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1 / 2))
  obtain ⟨r₂, hr₂⟩ := eventually_atTop.1 hsmall
  set R : ℝ := max r₀ (max r₁ (max r₂ 1)) with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le hr₀ (le_max_left _ _)
  have hmaj' : IntegrableOn (fun r => r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|)
      (Ioi R) :=
    hmaj.mono_set (Ioi_subset_Ioi (le_trans (le_max_left _ _) (le_max_right _ _)))
  refine ⟨hHmeas, R, hRpos, ?_⟩
  have hmaj2 : IntegrableOn
      (fun r => 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|)) (Ioi R) :=
    hmaj'.const_mul (2 * α)
  refine Integrable.mono hmaj2 (hHmeas.abs.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hrR : R ≤ r := le_of_lt hr
  have hr0 : r₀ ≤ r := le_trans (le_max_left _ _) hrR
  have hs1 : r₂ ≤ max r₂ 1 := le_max_left _ _
  have hs2 : max r₂ 1 ≤ max r₁ (max r₂ 1) := le_max_right _ _
  have hs3 : max r₁ (max r₂ 1) ≤ max r₀ (max r₁ (max r₂ 1)) := le_max_right _ _
  have hs4 : 1 ≤ max r₂ 1 := le_max_right _ _
  have hr2 : r₂ ≤ r := le_trans (le_trans (le_trans hs1 hs2) hs3) hrR
  have hrone : 1 ≤ r := le_trans (le_trans (le_trans hs4 hs2) hs3) hrR
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrone
  set J : ℝ := r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1) with hJ
  have hden_eq : (1 - α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) = 1 - α * J := by
    have h1 : α * r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)
        = α * (r ^ α * ∫ s in Ioi r, h s * s ^ (-α - 1)) := by ring
    rw [h1, ← hJ]
  have hHform : 1 + (A / α * r ^ (-α) * f r - 1) = (1 - α * J)⁻¹ := by
    have h := one_add_error_eq hA hα hr₀ hderiv hpos hinf hode hmeas hC r hr0
    rw [hden_eq] at h
    exact h
  have hy : A / α * r ^ (-α) * f r = (1 - α * J)⁻¹ := by linarith [hHform]
  have hdenne : 1 - α * J ≠ 0 := by
    intro hc
    rw [hc, inv_zero] at hy
    have h1 : 0 < A / α := by positivity
    have h2 : 0 < r ^ (-α) := Real.rpow_pos_of_pos hrpos _
    have h3 : 0 < f r := hpos r hr0
    have h4 : 0 < A / α * r ^ (-α) * f r := by positivity
    rw [hy] at h4
    exact lt_irrefl 0 h4
  have hHs : (A / α * r ^ (-α) * f r - 1) = α * J / (1 - α * J) := by
    rw [hy]
    field_simp
    ring
  have hsmallJ : |α * J| ≤ 1 / 2 := by
    have h3 := hr₂ r hr2
    simpa [hJ] using h3
  have hIbound : |J| ≤ r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s| := by
    have h1 : |∫ s in Ioi r, h s * s ^ (-α - 1)|
        ≤ ∫ s in Ioi r, |h s * s ^ (-α - 1)| := abs_integral_le_integral_abs
    have h2 : ∫ s in Ioi r, |h s * s ^ (-α - 1)| = ∫ s in Ioi r, s ^ (-α - 1) * |h s| := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := lt_trans hrpos hs
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _)]
      ring
    calc |J| = r ^ α * |∫ s in Ioi r, h s * s ^ (-α - 1)| := by
          rw [hJ, abs_mul, abs_of_nonneg (Real.rpow_nonneg hrpos.le _)]
      _ ≤ r ^ α * ∫ s in Ioi r, |h s * s ^ (-α - 1)| := by
          exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hrpos.le _)
      _ = r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s| := by rw [h2]
  have hden_lb : 1 / 2 ≤ |1 - α * J| := by
    have h2 : (1 : ℝ) - |α * J| ≤ |1 - α * J| := by
      have h3 := abs_sub_abs_le_abs_sub (1 : ℝ) (α * J)
      rw [abs_one] at h3
      linarith
    linarith
  have hnum : |α * J / (1 - α * J)| ≤ 2 * α * |J| := by
    rw [abs_div, abs_mul, abs_of_pos hα]
    have h2 : α * |J| / |1 - α * J| ≤ α * |J| / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden_lb
    have h3 : α * |J| / (1 / 2) = 2 * (α * |J|) := by field_simp
    linarith
  have hmain : |A / α * r ^ (-α) * f r - 1| / r
      ≤ 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
    rw [hHs]
    have h1 : |α * J / (1 - α * J)| / r ≤ (2 * α * |J|) / r :=
      div_le_div_of_nonneg_right hnum hrpos.le
    have h2 : (2 * α * |J|) / r
        ≤ 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
      have h3 : 2 * α * |J| / r ≤ 2 * α * (r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) / r := by
        gcongr
      have h4 : 2 * α * (r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) / r
          = 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
        have hrr : r ^ α / r = r ^ (α - 1) := (Real.rpow_sub_one hrpos.ne' α).symm
        calc 2 * α * (r ^ α * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) / r
            = 2 * α * ((r ^ α / r) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
              field_simp
          _ = 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by rw [hrr]
      linarith [h3, le_of_eq h4]
    linarith [h1, h2]
  have hrhs_nn : 0 ≤ 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
    have h1 : 0 ≤ ∫ s in Ioi r, s ^ (-α - 1) * |h s| := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs0 : 0 < s := lt_trans hrpos hs
      positivity
    have h2 : 0 ≤ r ^ (α - 1) := Real.rpow_nonneg hrpos.le _
    have h3 : 0 < α := hα
    have h4 : 0 ≤ r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s| := mul_nonneg h2 h1
    have h5 : 0 ≤ 2 * α := by positivity
    exact mul_nonneg h5 h4
  have h2 : ‖2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|)‖
      = 2 * α * (r ^ (α - 1) * ∫ s in Ioi r, s ^ (-α - 1) * |h s|) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hrhs_nn]
  rw [Real.norm_eq_abs, h2, abs_div, abs_of_pos hrpos]
  simpa using hmain

end ExactSolution

end PercLib.CriticalLRP.VolumeMoments.FirstMoment
