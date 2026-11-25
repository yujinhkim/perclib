/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Potter bounds and level comparison for regular variation

For a positive-index family with symmetric Potter bounds on an eventual domain,
`tendsto_div_of_potter` compares two level selections whose levels have positive
bounded ratios. The level selections `u` and `v` are explicitly required to tend
to infinity, and their future domain can be at least `X`. Those requirements are
what lets the Potter threshold move past any finite obstruction. No monotonicity
of the underlying regularly varying function is assumed.

This is a level-comparison component, not a proof that a generalized inverse exists
for an arbitrary regularly varying function. The monotone-continuous inverse
construction and a symmetric Potter comparison are supplied by
`Analysis/RVInverseMonotone.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.RVInverseMonotone
public import PercLib.CriticalLRP.Analysis.UniformConvergence

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

/-! ## The general scale-selection lemma (Potter's bounds, no monotonicity) -/

/-- Auxiliary: for `0 < b` and `b^ρ < c` there is a small `ε > 0` with
`ε ≤ 1/2`, `ε < ρ` and `(1+2ε) · max (b^{ρ-ε}) (b^{ρ+ε}) < c`
(continuity in the exponent at `ε = 0`). -/
theorem exists_small_eps_max {b ρ c : ℝ} (hb : 0 < b) (hρ : 0 < ρ) (hbc : b ^ ρ < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε < ρ ∧
      (1 + 2 * ε) * max (b ^ (ρ - ε)) (b ^ (ρ + ε)) < c := by
  have hcont : ContinuousAt (fun e : ℝ => (1 + 2 * e) * max (b ^ (ρ - e)) (b ^ (ρ + e))) 0 := by
    have h1 : ContinuousAt (fun e : ℝ => b ^ (ρ - e)) 0 :=
      (Real.continuousAt_const_rpow (a := b) (b := ρ - 0) (ne_of_gt hb)).comp
        (by fun_prop : ContinuousAt (fun e : ℝ => ρ - e) 0)
    have h2 : ContinuousAt (fun e : ℝ => b ^ (ρ + e)) 0 :=
      (Real.continuousAt_const_rpow (a := b) (b := ρ + 0) (ne_of_gt hb)).comp
        (by fun_prop : ContinuousAt (fun e : ℝ => ρ + e) 0)
    have hlin : ContinuousAt (fun e : ℝ => 1 + 2 * e) 0 := by fun_prop
    exact hlin.mul (h1.max h2)
  have hφ0 : (fun e : ℝ => (1 + 2 * e) * max (b ^ (ρ - e)) (b ^ (ρ + e))) 0 = b ^ ρ := by
    simp
  have hev : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), (1 + 2 * e) * max (b ^ (ρ - e)) (b ^ (ρ + e)) < c := by
    have hlt : (1 + 2 * (0:ℝ)) * max (b ^ (ρ - 0)) (b ^ (ρ + 0)) < c := by
      rw [show (1 + 2 * (0:ℝ)) * max (b ^ (ρ - 0)) (b ^ (ρ + 0)) = b ^ ρ by simp]
      exact hbc
    exact (hcont.eventually (Iio_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
  have hev2 : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), e < min (1 / 2) ρ :=
    (eventually_lt_nhds (lt_min (by norm_num) hρ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨hε1, hε2⟩, hε0⟩ :=
    ((hev.and hev2).and (self_mem_nhdsWithin : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e ∈ Ioi 0)).exists
  exact ⟨ε, hε0, le_of_lt (lt_of_lt_of_le hε2 (min_le_left _ _)),
    lt_of_lt_of_le hε2 (min_le_right _ _), hε1⟩

/-- Auxiliary: for `0 < b` and `c < b^ρ` there is a small `ε > 0` with
`ε ≤ 1/2`, `ε < ρ` and `c < (1-ε) · min (b^{ρ-ε}) (b^{ρ+ε})`. -/
theorem exists_small_eps_min {b ρ c : ℝ} (hb : 0 < b) (hρ : 0 < ρ) (hbc : c < b ^ ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε < ρ ∧
      c < (1 - ε) * min (b ^ (ρ - ε)) (b ^ (ρ + ε)) := by
  have hcont : ContinuousAt (fun e : ℝ => (1 - e) * min (b ^ (ρ - e)) (b ^ (ρ + e))) 0 := by
    have h1 : ContinuousAt (fun e : ℝ => b ^ (ρ - e)) 0 :=
      (Real.continuousAt_const_rpow (a := b) (b := ρ - 0) (ne_of_gt hb)).comp
        (by fun_prop : ContinuousAt (fun e : ℝ => ρ - e) 0)
    have h2 : ContinuousAt (fun e : ℝ => b ^ (ρ + e)) 0 :=
      (Real.continuousAt_const_rpow (a := b) (b := ρ + 0) (ne_of_gt hb)).comp
        (by fun_prop : ContinuousAt (fun e : ℝ => ρ + e) 0)
    have hlin : ContinuousAt (fun e : ℝ => 1 - e) 0 := by fun_prop
    exact hlin.mul (h1.min h2)
  have hψ0 : (fun e : ℝ => (1 - e) * min (b ^ (ρ - e)) (b ^ (ρ + e))) 0 = b ^ ρ := by
    simp
  have hev : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), c < (1 - e) * min (b ^ (ρ - e)) (b ^ (ρ + e)) := by
    have hlt : c < (1 - (0:ℝ)) * min (b ^ (ρ - 0)) (b ^ (ρ + 0)) := by
      rw [show (1 - (0:ℝ)) * min (b ^ (ρ - 0)) (b ^ (ρ + 0)) = b ^ ρ by simp]
      exact hbc
    exact (hcont.eventually (Ioi_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
  have hev2 : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), e < min (1 / 2) ρ :=
    (eventually_lt_nhds (lt_min (by norm_num) hρ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨hε1, hε2⟩, hε0⟩ :=
    ((hev.and hev2).and (self_mem_nhdsWithin : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e ∈ Ioi 0)).exists
  exact ⟨ε, hε0, le_of_lt (lt_of_lt_of_le hε2 (min_le_left _ _)),
    lt_of_lt_of_le hε2 (min_le_right _ _), hε1⟩

/-- **Scale selection from Potter's bounds.**  No monotonicity of `f` is assumed:
Potter's bounds (BGT Theorem 1.5.6, the classical consequence of regular
variation for measurable functions) provide the comparison of levels instead. -/
theorem tendsto_div_of_potter {f : ℝ → ℝ} {ρ c₁ c₂ X : ℝ} (hρ : 0 < ρ) (hX1 : 1 ≤ X)
    (hpot : ∀ ε : ℝ, 0 < ε → ∃ X' : ℝ, 1 ≤ X' ∧ ∀ x y : ℝ, X' ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (ρ - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (ρ + ε) * |f y|)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    {g u v : ℝ → ℝ}
    (hg : ∀ᶠ h in atTop, 0 < g h)
    (huT : Tendsto u atTop atTop) (hvT : Tendsto v atTop atTop)
    (hu : ∀ᶠ h in atTop, X ≤ u h) (hv : ∀ᶠ h in atTop, X ≤ v h)
    (hfu : Tendsto (fun h => g h * f (u h)) atTop (𝓝 c₁))
    (hfv : Tendsto (fun h => g h * f (v h)) atTop (𝓝 c₂))
    (hc1 : 0 < c₁) (hc2 : 0 < c₂) :
    Tendsto (fun h => u h / v h) atTop (𝓝 ((c₁ / c₂) ^ (1 / ρ))) := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hc : 0 < c₁ / c₂ := div_pos hc1 hc2
  have habspos : 0 < (c₁ / c₂) ^ (1 / ρ) := Real.rpow_pos_of_pos hc _
  have hbase : ((c₁ / c₂) ^ (1 / ρ)) ^ ρ = c₁ / c₂ := by
    rw [← Real.rpow_mul hc.le, one_div_mul_cancel hρ.ne', Real.rpow_one]
  have hratio : Tendsto (fun h => f (u h) / f (v h)) atTop (𝓝 (c₁ / c₂)) := by
    have h := hfu.div hfv hc2.ne'
    refine h.congr' ?_
    filter_upwards [hg] with h hh
    exact mul_div_mul_left _ _ hh.ne'
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower bounds: eventually `b < u h / v h`
    intro b hb
    rcases le_or_gt b 0 with hb0 | hb0
    · filter_upwards [hu, hv] with h h1 h2
      have hu0 : 0 < u h := lt_of_lt_of_le hX0 h1
      have hv0 : 0 < v h := lt_of_lt_of_le hX0 h2
      have hpos' : 0 < u h / v h := div_pos hu0 hv0
      linarith
    · have hbρ : b ^ ρ < c₁ / c₂ := by
        rw [← hbase]
        exact Real.rpow_lt_rpow hb0.le hb hρ
      obtain ⟨ε, hε0, hε2, hερ, hεc⟩ := exists_small_eps_max hb0 hρ hbρ
      obtain ⟨Xε, hXε1, hXε⟩ := hpot ε hε0
      filter_upwards [huT.eventually (eventually_ge_atTop Xε),
        hvT.eventually (eventually_ge_atTop Xε),
        hratio.eventually (eventually_gt_nhds hεc), hu, hv] with h huε hvε hrat huu hvv
      by_contra hle
      push Not at hle
      have hcomp := potter_compare hε0 hε2 hXε1 hXε huε hvε
      have hupos : 0 < f (u h) := hpos _ huu
      have hvpos : 0 < f (v h) := hpos _ hvv
      have hq : 0 ≤ u h / v h :=
        div_nonneg (by linarith [hX0, huu]) (by linarith [hX0, hvv])
      have hmaxle : max ((u h / v h) ^ (ρ - ε)) ((u h / v h) ^ (ρ + ε))
          ≤ max (b ^ (ρ - ε)) (b ^ (ρ + ε)) := by
        apply max_le_max
        · exact Real.rpow_le_rpow hq hle (le_of_lt (by linarith : (0:ℝ) < ρ - ε))
        · exact Real.rpow_le_rpow hq hle (le_of_lt (by linarith : (0:ℝ) < ρ + ε))
      have hsmall : f (u h) ≤ (1 + 2 * ε) * max (b ^ (ρ - ε)) (b ^ (ρ + ε)) * f (v h) := by
        have h1 := hcomp.2
        rw [abs_of_pos hupos, abs_of_pos hvpos] at h1
        have hstep : (1 + 2 * ε) * max ((u h / v h) ^ (ρ - ε)) ((u h / v h) ^ (ρ + ε)) * f (v h)
            ≤ (1 + 2 * ε) * max (b ^ (ρ - ε)) (b ^ (ρ + ε)) * f (v h) := by
          have h0 : (0 : ℝ) ≤ 1 + 2 * ε := by linarith
          have h2 : (0 : ℝ) ≤ f (v h) := hvpos.le
          nlinarith [hmaxle, h0, h2, mul_le_mul_of_nonneg_left hmaxle h0]
        linarith [hstep, h1]
      have hdiv : f (u h) / f (v h) ≤ (1 + 2 * ε) * max (b ^ (ρ - ε)) (b ^ (ρ + ε)) := by
        rw [div_le_iff₀ hvpos]
        linarith [hsmall]
      linarith [hdiv, hrat]
  · -- upper bounds: eventually `u h / v h < b`
    intro b hb
    have hb0 : 0 < b := lt_trans habspos hb
    have hbρ : c₁ / c₂ < b ^ ρ := by
      rw [← hbase]
      exact Real.rpow_lt_rpow (Real.rpow_nonneg hc.le _) hb hρ
    obtain ⟨ε, hε0, hε2, hερ, hεc⟩ := exists_small_eps_min hb0 hρ hbρ
    obtain ⟨Xε, hXε1, hXε⟩ := hpot ε hε0
    filter_upwards [huT.eventually (eventually_ge_atTop Xε),
      hvT.eventually (eventually_ge_atTop Xε),
      hratio.eventually (eventually_lt_nhds hεc), hu, hv] with h huε hvε hrat huu hvv
    by_contra hge
    push Not at hge
    have hcomp := potter_compare hε0 hε2 hXε1 hXε huε hvε
    have hupos : 0 < f (u h) := hpos _ huu
    have hvpos : 0 < f (v h) := hpos _ hvv
    have hminle : min (b ^ (ρ - ε)) (b ^ (ρ + ε))
        ≤ min ((u h / v h) ^ (ρ - ε)) ((u h / v h) ^ (ρ + ε)) := by
      apply min_le_min
      · exact Real.rpow_le_rpow hb0.le hge (le_of_lt (by linarith : (0:ℝ) < ρ - ε))
      · exact Real.rpow_le_rpow hb0.le hge (le_of_lt (by linarith : (0:ℝ) < ρ + ε))
    have hbig : (1 - ε) * min (b ^ (ρ - ε)) (b ^ (ρ + ε)) * f (v h) ≤ f (u h) := by
      have h1 := hcomp.1
      rw [abs_of_pos hupos, abs_of_pos hvpos] at h1
      have hstep : (1 - ε) * min (b ^ (ρ - ε)) (b ^ (ρ + ε)) * f (v h)
          ≤ (1 - ε) * min ((u h / v h) ^ (ρ - ε)) ((u h / v h) ^ (ρ + ε)) * f (v h) := by
        have h0 : (0 : ℝ) ≤ 1 - ε := by linarith
        have h2 : (0 : ℝ) ≤ f (v h) := hvpos.le
        nlinarith [hminle, h0, h2, mul_le_mul_of_nonneg_left hminle h0]
      linarith [hstep, h1]
    have hdiv : (1 - ε) * min (b ^ (ρ - ε)) (b ^ (ρ + ε)) ≤ f (u h) / f (v h) := by
      rw [le_div_iff₀ hvpos]
      linarith [hbig]
    linarith [hdiv, hrat]

/-- **Level comparison from measurable regular variation alone.** Potter bounds are obtained
from the existing uniform convergence theorem, not supplied as a separate hypothesis. -/
theorem tendsto_div_of_regularlyVarying {f : ℝ → ℝ} {ρ c₁ c₂ X : ℝ} (hρ : 0 < ρ)
    (hX1 : 1 ≤ X) (hmeas : Measurable f) (hrv : RegularlyVaryingAtTop f ρ)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    {g u v : ℝ → ℝ} (hg : ∀ᶠ h in atTop, 0 < g h)
    (huT : Tendsto u atTop atTop) (hvT : Tendsto v atTop atTop)
    (hu : ∀ᶠ h in atTop, X ≤ u h) (hv : ∀ᶠ h in atTop, X ≤ v h)
    (hfu : Tendsto (fun h => g h * f (u h)) atTop (𝓝 c₁))
    (hfv : Tendsto (fun h => g h * f (v h)) atTop (𝓝 c₂))
    (hc1 : 0 < c₁) (hc2 : 0 < c₂) :
    Tendsto (fun h => u h / v h) atTop (𝓝 ((c₁ / c₂) ^ (1 / ρ))) :=
  tendsto_div_of_potter hρ hX1 (hasPotterBounds_of_regularlyVarying hmeas hrv) hpos hg huT hvT
    hu hv hfu hfv hc1 hc2

/-! ### Non-vacuity: exact levels for the identity function. -/

/-- The conclusion is nondegenerate at the identity regularly varying function: levels `2y` and `y`
have ratio 2, while the scaling law predicts the same value. -/
theorem level_ratio_identity_example :
    Tendsto (fun h : ℝ => (2 * h) / h) atTop (𝓝 ((2 / 1 : ℝ) ^ (1 / (1 : ℝ)))) := by
  have hmain := tendsto_div_of_regularlyVarying (f := fun x : ℝ => x) (ρ := 1)
    (c₁ := 2) (c₂ := 1) (X := 1) zero_lt_one le_rfl measurable_id
    (by simpa using regularlyVaryingAtTop_rpow 1)
    (fun x hx => by linarith) (g := fun y : ℝ => y⁻¹)
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy using inv_pos.2 hy)
    (u := fun y : ℝ => 2 * y) (v := fun y : ℝ => y)
    (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2)) tendsto_id
    (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy using by nlinarith)
    (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy using by linarith)
    (by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      field_simp [hy.ne'])
    (by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      field_simp [hy.ne'])
    (by norm_num) zero_lt_one
  simpa only [div_one, Real.rpow_one] using hmain
