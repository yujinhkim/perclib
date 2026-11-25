/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Karamata's integral theorem (Hutchcroft, *Critical long-range percolation I*,
Lemma I.2.10, p. 26, citing [47, Feller, Theorem VIII.9.1]):

If `f : (0,∞) → ℝ` is regularly varying of index `α > -1` then
`∫_1^r f(s) ds ∼ r f(r)/(α+1)` as `r → ∞`.

The classical proof (Feller) only uses the definition of regular variation
through **Potter's bounds** (Bingham–Goldie–Teugels, Theorem 1.5.6):

  ∀ ε > 0 ∃ X, ∀ x ≥ y ≥ X,
    (1-ε)(x/y)^{α-ε}|f y| ≤ |f x| ≤ (1+ε)(x/y)^{α+ε}|f y|.

Potter's bounds are *not* proved here from `RegularlyVaryingAtTop`; the
derivation of Potter's bounds from regular variation goes through the uniform
convergence theorem (BGT Theorem 1.2.1), which is not in Mathlib.  So `hpot`
below is the single classical input of this file, exactly as in the paper's
citation of Feller.  Everything else here is proved.
-/
module

public import PercLib.CriticalLRP.Analysis.RegularVariation

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

/-- **Potter's bounds** (BGT Theorem 1.5.6), taken as an explicit hypothesis. -/
def HasPotterBounds (f : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 1 ≤ X ∧ ∀ x y : ℝ, X ≤ y → y ≤ x →
    (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
      |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y|

theorem potter_upper {f : ℝ → ℝ} {α ε X : ℝ}
    (h : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y|)
    {x y : ℝ} (hy : X ≤ y) (hxy : y ≤ x) :
    |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y| :=
  (h x y hy hxy).2

theorem potter_lower {f : ℝ → ℝ} {α ε X : ℝ}
    (h : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y|)
    {x y : ℝ} (hy : X ≤ y) (hxy : y ≤ x) :
    (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| :=
  (h x y hy hxy).1

/-- If `f` is eventually non-zero and satisfies Potter's bounds of index `α > -1`,
then `|f|` is at least a positive power of `r`, so `r f r → ∞`. -/
theorem tendsto_r_mul_of_potter {f : ℝ → ℝ} {α : ℝ} (hα : -1 < α)
    (hposf : ∀ᶠ x in atTop, 0 < f x) (hpot : HasPotterBounds f α) :
    Tendsto (fun r => r * f r) atTop atTop := by
  have hα4 : (0:ℝ) < (α + 1) / 4 := by linarith
  obtain ⟨η, hη0, hη1a, hη1b⟩ : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ η < (α + 1) / 2 := by
    refine ⟨min (1/2) ((α + 1) / 4), lt_min (by norm_num) hα4, ?_, ?_⟩
    · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    · calc min (1/2) ((α + 1) / 4) ≤ (α + 1) / 4 := min_le_right _ _
        _ < (α + 1) / 2 := by linarith
  obtain ⟨X₀, hX₀1, hX₀⟩ := hpot η hη0
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hposf
  set X := max X₀ X₁ with hXdef
  have hX1 : 1 ≤ X := le_trans hX₀1 (le_max_left _ _)
  have hXX₀ : X₀ ≤ X := le_max_left _ _
  have hneX : 0 < f X := hX₁ X (le_max_right _ _)
  have hpos : 0 < |f X| := abs_pos.2 (ne_of_gt hneX)
  -- for `s ≥ X`, `|f s| ≥ c s^{α-η}`
  have hc : 0 < (1 - η) * X ^ (-(α - η)) * |f X| := by
    have h1 : 0 < 1 - η := by linarith
    have h2 : 0 < X ^ (-(α - η)) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hbound : ∀ s : ℝ, X ≤ s →
      (1 - η) * X ^ (-(α - η)) * |f X| * s ^ (α - η) ≤ |f s| := by
    intro s hs
    have h1 := potter_lower hX₀ hXX₀ hs
    have h2 : (s / X) ^ (α - η) = s ^ (α - η) * X ^ (-(α - η)) := by
      rw [Real.div_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith)]
      ring
    rw [h2] at h1
    calc (1 - η) * X ^ (-(α - η)) * |f X| * s ^ (α - η)
        = (1 - η) * (s ^ (α - η) * X ^ (-(α - η))) * |f X| := by ring
      _ ≤ |f s| := h1
  -- so `s |f s| ≥ c s^{1+α-η} → ∞`
  rw [tendsto_atTop_atTop]
  intro b
  have hexp : 0 < 1 + α - η := by linarith
  have h2 : Tendsto (fun s : ℝ => (1 - η) * X ^ (-(α - η)) * |f X| * s ^ (1 + α - η))
      atTop atTop := by
    have h3 : Tendsto (fun s : ℝ => s ^ (1 + α - η)) atTop atTop :=
      tendsto_rpow_atTop hexp
    exact h3.const_mul_atTop hc
  obtain ⟨R, hR⟩ := (tendsto_atTop_atTop.1 h2) (max b 1)
  refine ⟨max R X, fun r hr => ?_⟩
  have hrR : R ≤ r := le_trans (le_max_left _ _) hr
  have hrX : X ≤ r := le_trans (le_max_right _ _) hr
  have hr1 : 1 ≤ r := le_trans hX1 hrX
  have h4 := hR r hrR
  have h5 : (1 - η) * X ^ (-(α - η)) * |f X| * r ^ (1 + α - η)
      = r * ((1 - η) * X ^ (-(α - η)) * |f X| * r ^ (α - η)) := by
    rw [show 1 + α - η = α - η + 1 by ring,
      Real.rpow_add (by linarith : (0:ℝ) < r) (α - η) 1, Real.rpow_one]
    ring
  rw [h5] at h4
  have h6 := hbound r hrX
  have hr0 : 0 < r := by linarith
  have h7 : r * ((1 - η) * X ^ (-(α - η)) * |f X| * r ^ (α - η)) ≤ r * |f r| := by
    have hnn : 0 ≤ (1 - η) * X ^ (-(α - η)) * |f X| * r ^ (α - η) := by
      have : 0 ≤ r ^ (α - η) := Real.rpow_nonneg hr0.le _
      have : 0 < 1 - η := by linarith
      positivity
    exact mul_le_mul_of_nonneg_left h6 hr0.le
  have hfrpos : 0 < f r := hX₁ r (le_trans (le_max_right _ _) hrX)
  have h8 : r * |f r| ≤ r * f r := by
    rw [abs_of_pos hfrpos]
  have : b ≤ r * |f r| := le_trans (le_max_left b 1) (le_trans h4 h7)
  linarith [h8]

/-- **Upper block.** For `0 < δ < 1`, the integral over `[δr, r]` satisfies
`(∫_{δr}^r f)/(r f(r)) → (1-δ^{α+1})/(α+1)`. -/
theorem tendsto_upper_block {f : ℝ → ℝ} {α η X δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1/2) (hαη : -1 < α - η) (hXpos : 0 < X)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hpotX : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - η) * (x / y) ^ (α - η) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + η) * (x / y) ^ (α + η) * |f y|)
    (hmeas : Measurable f)
    (hfpos : ∀ s : ℝ, X ≤ s → 0 < f s)
    (hrv : ∀ l : ℝ, 0 < l → Tendsto (fun x => f (l * x) / f x) atTop (𝓝 (l ^ α))) :
    Tendsto (fun r => ∫ u in δ..1, f (r * u) / f r) atTop
      (𝓝 ((1 - δ ^ (α + 1)) / (α + 1))) := by
  have hmain : Tendsto (fun r : ℝ => ∫ u in δ..1, f (r * u) / f r) atTop
      (𝓝 (∫ u in δ..1, u ^ α)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun u => 2 * u ^ (α - η)) ?_ ?_ ?_ ?_
    · filter_upwards with r
      exact ((hmeas.comp (measurable_const.mul measurable_id)).div_const _).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (X / δ)] with r hr
      filter_upwards with u hu
      rw [uIoc_of_le hδ1.le] at hu
      have hr0 : 0 < r := lt_of_lt_of_le (div_pos hXpos hδ0) hr
      have hu0 : 0 < u := lt_trans hδ0 hu.1
      have hrueq : r * u ≤ r := by nlinarith [hu.2]
      have hruX : X ≤ r * u := by
        have h1 : X ≤ r * δ := by
          rw [div_le_iff₀ hδ0] at hr
          linarith
        nlinarith [hu.1.le]
      have hlow := potter_lower hpotX hruX hrueq
      have hratio : (r / (r * u)) ^ (α - η) = u ^ (-(α - η)) := by
        have h1 : r / (r * u) = u⁻¹ := by field_simp
        rw [h1, Real.inv_rpow hu0.le, ← Real.rpow_neg hu0.le]
      rw [hratio, Real.rpow_neg hu0.le] at hlow
      have h3 : 0 < u ^ (α - η) := Real.rpow_pos_of_pos hu0 _
      have hlow' : (1 - η) * |f (r * u)| / u ^ (α - η) ≤ |f r| := by
        calc (1 - η) * |f (r * u)| / u ^ (α - η)
            = (1 - η) * (u ^ (α - η))⁻¹ * |f (r * u)| := by ring
          _ ≤ |f r| := hlow
      have hfr : 0 < f r := hfpos r (le_trans hruX hrueq)
      have h1 : |f (r * u)| ≤ |f r| * u ^ (α - η) / (1 - η) := by
        have hA : (1 - η) * |f (r * u)| ≤ |f r| * u ^ (α - η) := by
          rw [div_le_iff₀ h3] at hlow'
          linarith
        rw [le_div_iff₀ (by linarith : 0 < 1 - η)]
        linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hfr, div_le_iff₀ hfr]
      calc |f (r * u)| ≤ |f r| * u ^ (α - η) / (1 - η) := h1
        _ ≤ (2 * u ^ (α - η)) * f r := by
            rw [abs_of_pos hfr, div_le_iff₀ (by linarith : 0 < 1 - η)]
            have h4 : 0 ≤ u ^ (α - η) := Real.rpow_nonneg hu0.le _
            nlinarith [mul_nonneg h4 hfr.le]
    · have hcont : ContinuousOn (fun u : ℝ => 2 * u ^ (α - η)) (uIcc δ 1) := by
        intro u hu
        have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ0 (by rw [uIcc_of_le hδ1.le] at hu; exact hu.1))
        exact ((Real.continuousAt_rpow_const u (α - η) (Or.inl hu0)).const_mul 2).continuousWithinAt
      exact hcont.intervalIntegrable
    · filter_upwards with u hu
      rw [uIoc_of_le hδ1.le] at hu
      have := hrv u (lt_trans hδ0 hu.1)
      simpa [mul_comm] using this
  have hval : ∫ u in δ..1, u ^ α = (1 - δ ^ (α + 1)) / (α + 1) := by
    have hzero : (0:ℝ) ∉ uIcc δ 1 := by
      rw [uIcc_of_le hδ1.le]
      exact fun h => (not_le.2 hδ0) h.1
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩), Real.one_rpow]
  rw [hval] at hmain
  exact hmain


/-
**Status of Lemma I.2.10.** The two halves of the classical proof are proved above:

* `tendsto_upper_block` : for fixed `0 < δ < 1`,
  `∫_δ^1 f(r u) du / f(r) → (1-δ^{α+1})/(α+1)` (dominated convergence plus Potter);
* `lower_block_bound` : `∫_X^{δr} |f| ≤ 2δ^{α+1-η}/(α+1-η) · r f(r)` eventually
  (Potter's bound converted into a pointwise estimate and integrated with `∫_X^{δr} s^{α-η} ds`);
* `tendsto_r_mul_of_potter` : `r f(r) → ∞`.

What is *not* yet formalized is only the final ε-bookkeeping: splitting
`∫_1^r = ∫_1^{δr} + ∫_{δr}^r`, using `∫_{δr}^r f = r ∫_δ^1 f(ru) du`, and
letting first `r → ∞` and then `δ → 0`.  No mathematical ingredient is missing;
it is the (tedious) assembly of the three proven blocks.
-/
/-- **Lower block.** If `f` is locally integrable on `(0,∞)` then
`∫_X^{δr} |f| ≤ 2δ^{α+1-η}/(α+1-η) · r f(r)` eventually. -/
theorem lower_block_bound {f : ℝ → ℝ} {α η X δ : ℝ}
    (hη0 : 0 < η) (hη12 : η < 1/2) (hαη : -1 < α - η) (hXpos : 0 < X)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hloc : LocallyIntegrableOn f (Ioi 0))
    (hpotX : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - η) * (x / y) ^ (α - η) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + η) * (x / y) ^ (α + η) * |f y|)
    (hfpos : ∀ s : ℝ, X ≤ s → 0 < f s) :
    ∀ᶠ r in atTop, ∫ s in X..δ * r, |f s|
      ≤ (2 * δ ^ (α + 1 - η) / (α + 1 - η)) * (r * f r) := by
  filter_upwards [eventually_ge_atTop (X / δ), eventually_gt_atTop (0:ℝ)] with r hr hr0
  have hXδr : X ≤ δ * r := by
    rw [div_le_iff₀ hδ0] at hr
    linarith
  have hδr0 : 0 < δ * r := by positivity
  have hδr_le : δ * r ≤ r := by nlinarith
  have hXr : X ≤ r := le_trans hXδr hδr_le
  have hfr : 0 < f r := hfpos r hXr
  -- integrability of `|f|` on `[X, δr]`
  have hIntf : IntervalIntegrable (fun s => |f s|) volume X (δ * r) := by
    have h1 : IntegrableOn (fun s => |f s|) (Icc X (δ * r)) volume := by
      have h2 : IntegrableOn f (Icc X (δ * r)) volume :=
        (locallyIntegrableOn_iff (isLocallyClosed_Ioi) |>.1 hloc) (Icc X (δ*r))
          (fun x hx => lt_of_lt_of_le hXpos hx.1) isCompact_Icc
      exact h2.abs
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hXδr (by simp)).2 h1
  -- integrability of the comparison function
  have hIntg : IntervalIntegrable
      (fun s : ℝ => 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η)) volume X (δ * r) := by
    have hcont : ContinuousOn (fun s : ℝ => s ^ (α - η)) (uIcc X (δ * r)) := by
      intro s hs
      rw [uIcc_of_le hXδr] at hs
      exact (Real.continuousAt_rpow_const s (α - η)
        (Or.inl (ne_of_gt (lt_of_lt_of_le hXpos hs.1)))).continuousWithinAt
    have h2 : ContinuousOn (fun s : ℝ => 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η))
        (uIcc X (δ * r)) := by
      have h3 := hcont.const_mul (2 * |f r| * r ^ (-(α - η)))
      simpa [mul_assoc] using h3
    exact h2.intervalIntegrable
  -- pointwise comparison
  have hpt : ∀ s ∈ Icc X (δ * r),
      |f s| ≤ 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hXpos hs.1
    have hlow := potter_lower hpotX (x := r) (y := s) hs.1 (le_trans hs.2 hδr_le)
    have hratio : (r / s) ^ (α - η) = r ^ (α - η) * (s ^ (α - η))⁻¹ := by
      rw [Real.div_rpow (le_of_lt hr0) hs0.le, div_eq_mul_inv]
    rw [hratio] at hlow
    have hpos1 : 0 < 1 - η := by linarith
    have h3 : 0 < r ^ (α - η) := Real.rpow_pos_of_pos hr0 _
    have h4 : 0 < s ^ (α - η) := Real.rpow_pos_of_pos hs0 _
    -- multiply `hlow` by `s^{α-η}`
    have h5 : (1 - η) * r ^ (α - η) * |f s| ≤ |f r| * s ^ (α - η) := by
      have h6 := mul_le_mul_of_nonneg_right hlow h4.le
      have h7 : (1 - η) * (r ^ (α - η) * (s ^ (α - η))⁻¹) * |f s| * s ^ (α - η)
          = (1 - η) * r ^ (α - η) * |f s| := by
        field_simp
      linarith [h6, h7 ▸ h6]
    -- divide by `(1-η) r^{α-η}`
    have h8 : |f s| ≤ |f r| * s ^ (α - η) / ((1 - η) * r ^ (α - η)) := by
      rw [le_div_iff₀ (by positivity : 0 < (1 - η) * r ^ (α - η))]
      linarith
    have h9 : |f r| * s ^ (α - η) / ((1 - η) * r ^ (α - η))
        = ((1 - η)⁻¹ * |f r| * r ^ (-(α - η))) * s ^ (α - η) := by
      rw [Real.rpow_neg (le_of_lt hr0)]
      field_simp
    have h10 : (1 - η)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith : (0:ℝ) < 1 - η) (by norm_num : (0:ℝ) < 2)]
      linarith
    have hnn : 0 ≤ |f r| * r ^ (-(α - η)) * s ^ (α - η) := by positivity
    calc |f s| ≤ ((1 - η)⁻¹ * |f r| * r ^ (-(α - η))) * s ^ (α - η) := by rw [← h9]; exact h8
      _ ≤ 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η) := by
          nlinarith [h10, hnn]
  have hmono := intervalIntegral.integral_mono_on hXδr hIntf hIntg hpt
  -- evaluate the comparison integral
  have hzero : (0:ℝ) ∉ uIcc X (δ * r) := by
    rw [uIcc_of_le hXδr]
    exact fun h => (not_le.2 hXpos) h.1
  have hInt : ∫ s in X..δ * r, s ^ (α - η) = ((δ * r) ^ (α - η + 1) - X ^ (α - η + 1)) / (α - η + 1) := by
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩)]
  have hInt_le : ∫ s in X..δ * r, s ^ (α - η) ≤ (δ * r) ^ (α - η + 1) / (α - η + 1) := by
    rw [hInt]
    have hXpow : 0 ≤ X ^ (α - η + 1) := Real.rpow_nonneg hXpos.le _
    have hden : 0 < α - η + 1 := by linarith
    have hle : ((δ * r) ^ (α - η + 1) - X ^ (α - η + 1)) ≤ (δ * r) ^ (α - η + 1) := by
      linarith
    exact div_le_div_of_nonneg_right hle hden.le
  have hIntg_val : ∫ s in X..δ * r, 2 * |f r| * r ^ (-(α - η)) * s ^ (α - η)
      = 2 * |f r| * r ^ (-(α - η)) * ∫ s in X..δ * r, s ^ (α - η) := by
    rw [intervalIntegral.integral_const_mul]
  calc ∫ s in X..δ * r, |f s|
      ≤ 2 * |f r| * r ^ (-(α - η)) * ∫ s in X..δ * r, s ^ (α - η) := by
        rw [← hIntg_val]; exact hmono
    _ ≤ 2 * |f r| * r ^ (-(α - η)) * ((δ * r) ^ (α - η + 1) / (α - η + 1)) := by
        have hnn : 0 ≤ 2 * |f r| * r ^ (-(α - η)) := by positivity
        exact mul_le_mul_of_nonneg_left hInt_le hnn
    _ = (2 * δ ^ (α + 1 - η) / (α + 1 - η)) * (r * f r) := by
        rw [abs_of_pos hfr, Real.rpow_neg (le_of_lt hr0), Real.mul_rpow (le_of_lt hδ0) hr0.le]
        rw [show α - η + 1 = α + 1 - η by ring,
          show α + 1 - η = (α - η) + 1 by ring,
          Real.rpow_add hr0 (α - η) 1, Real.rpow_one]
        field_simp



end PercLib.CriticalLRP.Analysis
