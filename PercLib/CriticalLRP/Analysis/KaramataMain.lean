/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The final assembly of Lemma I.2.10 (Karamata's integral theorem) from the two
blocks proved in `Karamata.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.Karamata

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

/-- **Lemma I.2.10 (Karamata's integral theorem; Feller VIII.9.1).**
If `f` is measurable, locally integrable on `(0,∞)`, eventually positive, regularly
varying of index `α > -1`, and satisfies Potter's bounds, then
`∫_1^r f ∼ r f(r)/(α+1)`. -/
theorem lemma_I_2_10 {f : ℝ → ℝ} {α : ℝ} (hα : -1 < α)
    (hmeas : Measurable f) (hloc : LocallyIntegrableOn f (Ioi 0))
    (hposf : ∀ᶠ x in atTop, 0 < f x)
    (hrv : RegularlyVaryingAtTop f α)
    (hpot : HasPotterBounds f α) :
    Tendsto (fun r => (∫ s in 1..r, f s) / (r * f r)) atTop (𝓝 (1 / (α + 1))) := by
  classical
  have hα4 : (0:ℝ) < (α + 1) / 4 := by linarith
  obtain ⟨η, hη0, hη12, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η < 1/2 ∧ η < (α + 1) / 2 := by
    refine ⟨min (1/4) ((α + 1) / 4), ?_, ?_, ?_⟩
    · exact lt_min (by norm_num) hα4
    · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    · calc min (1/4) ((α + 1) / 4) ≤ (α + 1) / 4 := min_le_right _ _
        _ < (α + 1) / 2 := by linarith
  have hαη : -1 < α - η := by linarith
  obtain ⟨X₀, hX₀1, hX₀⟩ := hpot η hη0
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 hposf
  set X : ℝ := max X₀ X₁ with hXdef
  have hX1 : 1 ≤ X := le_trans hX₀1 (le_max_left _ _)
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX1
  have hpotX : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - η) * (x / y) ^ (α - η) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + η) * (x / y) ^ (α + η) * |f y| :=
    fun x y hy hxy => hX₀ x y (le_trans (le_max_left _ _) hy) hxy
  have hfpos : ∀ s : ℝ, X ≤ s → 0 < f s :=
    fun s hs => hX₁ s (le_trans (le_max_right _ _) hs)
  have hrv' : ∀ l : ℝ, 0 < l → Tendsto (fun x => f (l * x) / f x) atTop (𝓝 (l ^ α)) := hrv.2
  have hbig : Tendsto (fun r => r * f r) atTop atTop := tendsto_r_mul_of_potter hα hposf hpot
  -- interval integrability on every `[p,q] ⊂ (0,∞)`
  have hIntf : ∀ p q : ℝ, 0 < p → p ≤ q → IntervalIntegrable f volume p q := by
    intro p q hp hpq
    have h1 : IntegrableOn f (Icc p q) volume :=
      (locallyIntegrableOn_iff (isLocallyClosed_Ioi) |>.1 hloc) (Icc p q)
        (fun x hx => lt_of_lt_of_le hp hx.1) isCompact_Icc
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpq (by simp)).2 h1
  -- limits at `δ → 0`
  have hpow0 : ∀ s : ℝ, 0 < s → Tendsto (fun δ : ℝ => δ ^ s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    intro s hs
    have h1 : Tendsto (fun δ : ℝ => δ ^ (-s)) (𝓝[>] (0:ℝ)) atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith)
    have h2 : Tendsto (fun δ : ℝ => (δ ^ (-s))⁻¹) (𝓝[>] (0:ℝ)) (𝓝 0) := h1.inv_tendsto_atTop
    exact h2.congr' (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      rw [Real.rpow_neg (le_of_lt hδ), inv_inv])
  have hlimA : Tendsto (fun δ : ℝ => 2 * δ ^ (α + 1 - η) / (α + 1 - η)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 := hpow0 (α + 1 - η) (by linarith)
    simpa using (h1.const_mul 2).div_const (α + 1 - η)
  have hlimB : Tendsto (fun δ : ℝ => δ ^ (α + 1) / (α + 1)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 := hpow0 (α + 1) (by linarith)
    simpa using h1.div_const (α + 1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose `δ` with both budgets
  obtain ⟨δ, hδ0, hδ1, hδA, hδB⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      2 * δ ^ (α + 1 - η) / (α + 1 - η) < ε / 8 ∧ δ ^ (α + 1) / (α + 1) < ε / 8 := by
    obtain ⟨δA, hδApos, hδA⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlimA (ε/8) (by linarith)
    obtain ⟨δB, hδBpos, hδB⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlimB (ε/8) (by linarith)
    refine ⟨min (min (δA/2) (δB/2)) (1/2), lt_min (lt_min (by linarith) (by linarith)) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_, ?_⟩
    · have hpos : 0 < min (min (δA/2) (δB/2)) (1/2) :=
        lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      have hlt : min (min (δA/2) (δB/2)) (1/2) < δA := by
        have h2 : min (min (δA/2) (δB/2)) (1/2) ≤ δA/2 :=
          le_trans (min_le_left _ _) (min_le_left _ _)
        linarith
      have h2 := hδA hpos (by rw [Real.dist_eq, sub_zero, abs_of_pos hpos]; exact hlt)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : 0 ≤ 2 * (min (min (δA/2) (δB/2)) (1/2)) ^ (α + 1 - η) / (α + 1 - η) := by
        have h4 : 0 < α + 1 - η := by linarith
        positivity
      rwa [abs_of_nonneg h3] at h2
    · have hpos : 0 < min (min (δA/2) (δB/2)) (1/2) :=
        lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
      have hlt : min (min (δA/2) (δB/2)) (1/2) < δB := by
        have h2 : min (min (δA/2) (δB/2)) (1/2) ≤ δB/2 :=
          le_trans (min_le_left _ _) (min_le_right _ _)
        linarith
      have h2 := hδB hpos (by rw [Real.dist_eq, sub_zero, abs_of_pos hpos]; exact hlt)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : 0 ≤ (min (min (δA/2) (δB/2)) (1/2)) ^ (α + 1) / (α + 1) := by
        have h4 : 0 < α + 1 := by linarith
        positivity
      rwa [abs_of_nonneg h3] at h2
  -- the two blocks
  have hupper := tendsto_upper_block (f := f) hη0 hη12 hαη hXpos hδ0 hδ1 hpotX hmeas hfpos hrv'
  have hlowb := lower_block_bound (f := f) hη0 hη12 hαη hXpos hδ0 hδ1 hloc hpotX hfpos
  -- `|∫_1^X f| / (r f r) → 0`
  have hC₀ : ∀ᶠ r in atTop, |∫ s in 1..X, f s| / (r * f r) < ε / 8 := by
    have h1 : Tendsto (fun r : ℝ => |∫ s in 1..X, f s| / (r * f r)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun r : ℝ => (r * f r)⁻¹) atTop (𝓝 0) := hbig.inv_tendsto_atTop
      have h3 : Tendsto (fun r : ℝ => |∫ s in 1..X, f s| * (r * f r)⁻¹) atTop (𝓝 0) := by
        simpa using h2.const_mul (|∫ s in 1..X, f s|)
      exact h3.congr' (by filter_upwards with r; rw [div_eq_mul_inv])
    obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 h1 (ε/8) (by linarith)
    filter_upwards [eventually_ge_atTop R, eventually_ge_atTop X, eventually_gt_atTop (0:ℝ)]
      with r hr hrX hr0
    have h5 := hR r hr
    rw [Real.dist_eq, sub_zero] at h5
    rwa [abs_of_nonneg (by have hfr : 0 < f r := hfpos r hrX; positivity :
      (0:ℝ) ≤ |∫ s in 1..X, f s| / (r * f r))] at h5
  -- the lower block
  have hlow' : ∀ᶠ r in atTop, |(∫ s in 1..δ * r, f s) / (r * f r)| < ε / 4 := by
    filter_upwards [hC₀, hlowb, eventually_ge_atTop X, eventually_gt_atTop (0:ℝ),
      eventually_ge_atTop (X / δ)] with r hC hlowr hrX hr0 hrδ
    have hXδr : X ≤ δ * r := by
      rw [div_le_iff₀ hδ0] at hrδ
      linarith
    have hfr : 0 < f r := hfpos r hrX
    have hrfr : 0 < r * f r := by positivity
    have hsplit2 : ∫ s in 1..δ * r, f s = (∫ s in 1..X, f s) + (∫ s in X..δ * r, f s) := by
      simpa using (intervalIntegral.integral_add_adjacent_intervals
        (hIntf 1 X one_pos hX1) (hIntf X (δ * r) hXpos hXδr)).symm
    have habs : |∫ s in 1..δ * r, f s| ≤ |∫ s in 1..X, f s| + ∫ s in X..δ * r, |f s| := by
      rw [hsplit2]
      calc |(∫ s in 1..X, f s) + (∫ s in X..δ * r, f s)|
          ≤ |∫ s in 1..X, f s| + |∫ s in X..δ * r, f s| :=
              abs_add_le (∫ s in 1..X, f s) (∫ s in X..δ * r, f s)
        _ ≤ |∫ s in 1..X, f s| + ∫ s in X..δ * r, |f s| := by
            have h3 : |∫ s in X..δ * r, f s| ≤ ∫ s in X..δ * r, |f s| :=
              intervalIntegral.abs_integral_le_integral_abs hXδr
            linarith
    have h1 : |(∫ s in 1..δ * r, f s) / (r * f r)|
        = |∫ s in 1..δ * r, f s| / (r * f r) := by
      rw [abs_div, abs_of_pos hrfr]
    rw [h1]
    have h4 : (∫ s in X..δ * r, |f s|) / (r * f r) ≤ 2 * δ ^ (α + 1 - η) / (α + 1 - η) := by
      rw [div_le_iff₀ hrfr]
      linarith
    have h5 : |∫ s in 1..δ * r, f s| / (r * f r)
        ≤ (|∫ s in 1..X, f s| + ∫ s in X..δ * r, |f s|) / (r * f r) := by
      gcongr
    have h6 : (|∫ s in 1..X, f s| + ∫ s in X..δ * r, |f s|) / (r * f r)
        = |∫ s in 1..X, f s| / (r * f r) + (∫ s in X..δ * r, |f s|) / (r * f r) := by
      field_simp
    linarith
  -- assemble
  have hupper' : ∀ᶠ r in atTop,
      |(∫ u in δ..1, f (r * u) / f r) - (1 - δ ^ (α + 1)) / (α + 1)| < ε / 4 := by
    obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 hupper (ε/4) (by linarith)
    filter_upwards [eventually_ge_atTop R] with r hr
    have h5 := hR r hr
    rwa [Real.dist_eq] at h5
  have hfinal : ∀ᶠ r in atTop,
      |(∫ s in 1..r, f s) / (r * f r) - 1 / (α + 1)| < ε := by
    filter_upwards [hlow', hupper', eventually_ge_atTop (max X (1/δ)),
      eventually_ge_atTop (X/δ), eventually_gt_atTop (0:ℝ)] with r hlow hup hr hrδ hr0
    -- decomposition at this `r`
    have hXr : X ≤ r := le_trans (le_max_left _ _) hr
    have hinv : 1/δ ≤ r := le_trans (le_max_right _ _) hr
    have hδr0 : 0 < δ * r := by positivity
    have hδr1 : (1:ℝ) ≤ δ * r := by
      rw [div_le_iff₀ hδ0] at hinv
      linarith
    have hδrX : X ≤ δ * r := by
      rw [div_le_iff₀ hδ0] at hrδ
      linarith
    have hfr : 0 < f r := hfpos r hXr
    have hrfr : 0 < r * f r := by positivity
    have hsplit : ∫ s in 1..r, f s = (∫ s in 1..δ * r, f s) + (∫ s in δ * r..r, f s) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hIntf 1 (δ * r) one_pos hδr1) (hIntf (δ * r) r hδr0 (by nlinarith))).symm
    have hsub : (∫ s in δ * r..r, f s) / (r * f r) = ∫ u in δ..1, f (r * u) / f r := by
      have h := intervalIntegral.integral_comp_mul_left (a := δ) (b := 1) (c := r) f (ne_of_gt hr0)
      rw [smul_eq_mul] at h
      rw [show r * δ = δ * r by ring, show r * 1 = r by ring] at h
      rw [show (∫ u in δ..1, f (r * u) / f r) = (∫ u in δ..1, f (r * u)) / f r from
        intervalIntegral.integral_div (f r) (fun u => f (r * u)), h]
      field_simp
    have hdec : (∫ s in 1..r, f s) / (r * f r)
        = (∫ s in 1..δ * r, f s) / (r * f r) + ∫ u in δ..1, f (r * u) / f r := by
      rw [hsplit, add_div, hsub]
    rw [hdec]
    set A := (∫ s in 1..δ * r, f s) / (r * f r) with hAdef
    set B := ∫ u in δ..1, f (r * u) / f r with hBdef
    set d := (1 - δ ^ (α + 1)) / (α + 1) with hddef
    set c := 1 / (α + 1) with hcdef
    have hkey : A + B - c = A + (B - d) + (d - c) := by ring
    have h2 : |A + (B - d) + (d - c)| ≤ |A| + |B - d| + |d - c| := by
      calc |A + (B - d) + (d - c)| ≤ |A + (B - d)| + |d - c| := abs_add_le _ _
        _ ≤ (|A| + |B - d|) + |d - c| := by
            have h4 := abs_add_le A (B - d)
            linarith
    have hdc : |d - c| = δ ^ (α + 1) / (α + 1) := by
      rw [hddef, hcdef, div_sub_div_same,
        show (1 - δ ^ (α + 1)) - 1 = -δ ^ (α + 1) by ring,
        show -δ ^ (α + 1) / (α + 1) = -(δ ^ (α + 1) / (α + 1)) from neg_div _ _,
        abs_neg, abs_of_nonneg (div_nonneg (by positivity) (by linarith : (0:ℝ) ≤ α + 1))]
    have hdlt : |d - c| < ε / 8 := by rw [hdc]; exact hδB
    rw [hkey]
    have hAl : |A| < ε / 4 := by rw [hAdef]; exact hlow
    have hBl : |B - d| < ε / 4 := by rw [hBdef, hddef]; exact hup
    calc |A + (B - d) + (d - c)| ≤ |A| + |B - d| + |d - c| := h2
      _ < ε := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfinal
  exact ⟨N, fun n hn => by
    rw [Real.dist_eq]
    exact hN n hn⟩

end PercLib.CriticalLRP.Analysis
