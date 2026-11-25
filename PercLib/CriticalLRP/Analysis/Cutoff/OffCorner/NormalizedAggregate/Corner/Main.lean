/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated from the independently checked adversarial audit of the two-point capstone in
Ultramath `smwv4hzkh`, with repaired left-limit aggregation and one-sided/two-sided joining.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.Capstone
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.NormalizedAggregate.Corner.Defs

/-!
# Audit of the two-point capstone

* `cutPivotFactorLT`: the normalized pivotal factor seen from the left of `r`;
* `cutPivotFactor_eq_of_right_window`: on a corner-free right window the factor is frozen;
* `cutPivotFactor_eq_LT_of_left_window`: on a corner-free left window the factor is the
  left-hand factor;
* `tendsto_normalizedPivotMass_nhdsGT`: the normalized pivotal mass is right-continuous at
  every positive radius, with no off-corner hypothesis;
* `tendsto_normalizedPivotMass_nhdsLT_trimmed`: at every positive radius `r0` the left limit is the
  normalized pivotal mass with the activating shell at `r0` removed;
* `leftLimit_eq_value_iff_shell_eq_zero` and
  `continuousAt_iff_leftLimit_eq_value`: the off-corner hypothesis of the capstone is exactly
  the vanishing of the activation shell, so it is not removable for the normalized mass.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 0. Signature checks (audit trail) -/

#check @SourceModelData.continuousAt_normalizedPivotMass
#check @SourceModelData.continuousAt_forcedEvent
#check @SourceModelData.continuousAt_pivotalFlux_singleton
#check @SourceModelData.continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux
#check @SourceModelData.hcontinf_of_continuousAt_deriv_of_continuousAt_pivotalFlux
#check @SourceModelData.hasDerivAt_cutMassReal_rhsScalar_of_envelope_of_pivotalFlux
#check @SourceModelData.exists_gap_at_attainedRadii
#check @SourceModelData.cutMassAt_zero_eq_cutMoment
#check @SourceModelData.not_continuousAt_cutEdgeDeriv_at_dist
#check @tendsto_tsum_of_dominated_convergence
#check @Summable.of_nonneg_of_le
#check @Summable.tsum_add

/-! ## 1. The left-hand normalized pivotal factor -/

/-- The left/strict factor is defined in the independent `Corner.Defs` module. -/
theorem cutPivotFactorLT_nonneg (r : ℝ) (e : Sym2 M.V) : 0 ≤ M.cutPivotFactorLT r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutPivotFactorLT, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy]
      by_cases hs : M.S.dist x y < r
      · rw [ite_eq_left hs]
        exact (Real.exp_pos _).le
      · rw [ite_eq_right hs]

/-- The left factor is dominated by the two-sided one. -/
theorem cutPivotFactorLT_le (r : ℝ) (e : Sym2 M.V) :
    M.cutPivotFactorLT r e ≤ M.cutPivotFactor r e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutPivotFactorLT, radialSym_mk, cutPivotFactor, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      by_cases hs : M.S.dist x y < r
      · rw [ite_eq_left hs]
        by_cases hs' : M.S.dist x y ≤ r
        · rw [ite_eq_left hs']
        · exact absurd hs (not_lt.mpr (le_of_lt (not_le.mp hs')))
      · rw [ite_eq_right hs]
        by_cases hs' : M.S.dist x y ≤ r
        · rw [ite_eq_left hs']
          exact (Real.exp_pos _).le
        · rw [ite_eq_right hs']

/-- The two-sided factor is monotone in the radius. -/
theorem cutPivotFactor_mono_r {r r' : ℝ} (h : r ≤ r') (e : Sym2 M.V) :
    M.cutPivotFactor r e ≤ M.cutPivotFactor r' e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutPivotFactor, radialSym_mk, cutPivotFactor, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      by_cases hs : M.S.dist x y ≤ r
      · rw [ite_eq_left hs, ite_eq_left (le_trans hs h)]
      · rw [ite_eq_right hs]
        by_cases hs' : M.S.dist x y ≤ r'
        · rw [ite_eq_left hs']
          exact (Real.exp_pos _).le
        · rw [ite_eq_right hs']

/-! ## 2. The factor on corner-free one-sided windows -/

/-- On a right window containing no attained radius other than `r0`, the normalized pivotal
factor is frozen. -/
theorem cutPivotFactor_eq_of_right_window {r0 ε r : ℝ}
    (hε : ∀ s : ℝ, s ∈ M.attainedRadii → s ≠ r0 → ε ≤ |s - r0|)
    (hr : r0 < r) (hrε : r < r0 + ε) (e : Sym2 M.V) :
    M.cutPivotFactor r e = M.cutPivotFactor r0 e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutPivotFactor, radialSym_mk, cutPivotFactor, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      have hmem : M.S.dist x y ∈ M.attainedRadii := M.S.mem_attainedRadii_of_dist hxy
      rcases lt_trichotomy (M.S.dist x y) r0 with hlt | heq | hgt
      · have h1 : M.S.dist x y ≤ r := le_of_lt (hlt.trans hr)
        have h2 : M.S.dist x y ≤ r0 := le_of_lt hlt
        rw [ite_eq_left h1, ite_eq_left h2]
      · have h1 : M.S.dist x y ≤ r := by rw [heq]; exact le_of_lt hr
        have h2 : M.S.dist x y ≤ r0 := by rw [heq]
        rw [ite_eq_left h1, ite_eq_left h2]
      · have hge : r0 + ε ≤ M.S.dist x y := by
          have h := hε _ hmem (ne_of_gt hgt)
          rw [abs_of_pos (sub_pos.mpr hgt)] at h
          linarith
        have h1 : ¬ (M.S.dist x y ≤ r) := not_le.mpr (lt_of_lt_of_le hrε hge)
        have h2 : ¬ (M.S.dist x y ≤ r0) := not_le.mpr hgt
        rw [ite_eq_right h1, ite_eq_right h2]

/-- On a left window containing no attained radius other than `r0`, the two-sided factor is
the left-hand factor at `r0`. -/
theorem cutPivotFactor_eq_LT_of_left_window {r0 ε r : ℝ}
    (hε : ∀ s : ℝ, s ∈ M.attainedRadii → s ≠ r0 → ε ≤ |s - r0|)
    (hr : r0 - ε < r) (hr' : r < r0) (e : Sym2 M.V) :
    M.cutPivotFactor r e = M.cutPivotFactorLT r0 e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [cutPivotFactor, radialSym_mk, cutPivotFactorLT, radialSym_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      have hmem : M.S.dist x y ∈ M.attainedRadii := M.S.mem_attainedRadii_of_dist hxy
      rcases lt_trichotomy (M.S.dist x y) r0 with hlt | heq | hgt
      · have h1 : M.S.dist x y ≤ r := by
          have h := hε _ hmem (ne_of_lt hlt)
          rw [abs_of_neg (sub_neg.mpr hlt)] at h
          linarith
        have h2 : M.S.dist x y < r0 := hlt
        rw [ite_eq_left h1, ite_eq_left h2]
      · have h1 : ¬ (M.S.dist x y ≤ r) := by rw [heq]; exact not_le.mpr hr'
        have h2 : ¬ (M.S.dist x y < r0) := by rw [heq]; exact lt_irrefl r0
        rw [ite_eq_right h1, ite_eq_right h2]
      · have hge : r0 + ε ≤ M.S.dist x y := by
          have h := hε _ hmem (ne_of_gt hgt)
          rw [abs_of_pos (sub_pos.mpr hgt)] at h
          linarith
        have h1 : ¬ (M.S.dist x y ≤ r) := not_le.mpr (lt_trans hr' hgt)
        have h2 : ¬ (M.S.dist x y < r0) := not_lt.mpr (le_of_lt hgt)
        rw [ite_eq_right h1, ite_eq_right h2]


/-! ## 3. Right continuity at every positive radius (no off-corner hypothesis) -/

theorem tendsto_normalizedPivotMass_nhdsGT {y : M.V} {r0 R : ℝ}
    (hr0 : 0 < r0) (hr0R : r0 < R) (h1 : M.cutMoment 1 R ≠ ⊤) :
    Tendsto (M.normalizedPivotMass y) (𝓝[>] r0) (𝓝 (M.normalizedPivotMass y r0)) := by
  classical
  have hfin : M.cutMassAt R 0 ≠ ⊤ := by
    rw [M.cutMassAt_zero_eq_cutMoment]
    exact h1
  obtain ⟨ε, hε0, hε⟩ := M.exists_gap_at_attainedRadii r0
  set δ : ℝ := min (min ε (R - r0)) (r0 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hε0 (sub_pos.mpr hr0R)) (by linarith)
  have hδε : δ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hδR : δ ≤ R - r0 := (min_le_left _ _).trans (min_le_right _ _)
  have hδr : δ ≤ r0 / 2 := min_le_right _ _
  have hwin : Set.Ioo r0 (r0 + δ) ∈ 𝓝[>] r0 := Ioo_mem_nhdsGT (by linarith)
  have hfac : ∀ᶠ r : ℝ in 𝓝[>] r0, ∀ e : Sym2 M.V,
      M.cutPivotFactor r e = M.cutPivotFactor r0 e := by
    filter_upwards [hwin] with r hr e
    exact M.cutPivotFactor_eq_of_right_window (r0 := r0) (ε := ε) hε hr.1
      (by linarith [hr.2, hδε]) e
  have hrlt : ∀ᶠ r : ℝ in 𝓝[>] r0, r < R ∧ 0 < r := by
    filter_upwards [hwin] with r hr
    exact ⟨by linarith [hr.2, hδR], by linarith [hr.1]⟩
  have hsumm : Summable (M.pivotMajorant r0 R) := M.summable_pivotMajorant h1
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] r0, ∀ e : Sym2 M.V,
      ‖M.cutPivotFactor r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖
        ≤ M.pivotMajorant r0 R e := by
    filter_upwards [hrlt] with r hr
    intro e
    have hpivnonneg : 0 ≤ pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω
    have hnn : 0 ≤ M.cutPivotFactor r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e :=
      mul_nonneg (M.cutPivotFactor_nonneg r0 e) hpivnonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc M.cutPivotFactor r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
        ≤ M.cutPivotFactor r0 e * M.edgeTouchMass r e :=
          mul_le_mul_of_nonneg_left (M.pivotalFlux_singleton_le_edgeTouchMass y e)
            (M.cutPivotFactor_nonneg r0 e)
      _ ≤ M.cutPivotFactor r0 e * M.edgeTouchMass R e :=
          mul_le_mul_of_nonneg_left (M.edgeTouchMass_mono hr.2 (lt_trans hr0 hr0R) hr.1.le e)
            (M.cutPivotFactor_nonneg r0 e)
      _ = M.pivotMajorant r0 R e := rfl
  have htend : Tendsto (fun r => ∑' e : Sym2 M.V, M.cutPivotFactor r0 e *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) (𝓝[>] r0)
      (𝓝 (∑' e : Sym2 M.V, M.cutPivotFactor r0 e *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := M.pivotMajorant r0 R) hsumm ?_ hbound
    intro e
    by_cases hs : inSupport M r0 e
    · exact ((M.continuousAt_pivotalFlux_singleton hr0 hr0R hfin y e).tendsto.mono_left
        nhdsWithin_le_nhds).const_mul (M.cutPivotFactor r0 e)
    · have hzero : M.cutPivotFactor r0 e = 0 := M.cutPivotFactor_eq_zero_of_not_inSupport r0 hs
      simp only [hzero, zero_mul]
      exact tendsto_const_nhds
  refine htend.congr' ?_
  filter_upwards [hfac] with r hr
  rw [normalizedPivotMass]
  exact tsum_congr fun e => by rw [hr e]

/-! ## 4. The left limit at every positive radius -/

theorem tendsto_normalizedPivotMass_nhdsLT_trimmed {y : M.V} {r0 R : ℝ}
    (hr0 : 0 < r0) (hr0R : r0 < R) (h1 : M.cutMoment 1 R ≠ ⊤) :
    Tendsto (M.normalizedPivotMass y) (𝓝[<] r0)
      (𝓝 (∑' e : Sym2 M.V, M.cutPivotFactorLT r0 e *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)) := by
  classical
  have hfin : M.cutMassAt R 0 ≠ ⊤ := by
    rw [M.cutMassAt_zero_eq_cutMoment]
    exact h1
  obtain ⟨ε, hε0, hε⟩ := M.exists_gap_at_attainedRadii r0
  set δ : ℝ := min (min ε (R - r0)) (r0 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hε0 (sub_pos.mpr hr0R)) (by linarith)
  have hδε : δ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hδR : δ ≤ R - r0 := (min_le_left _ _).trans (min_le_right _ _)
  have hδr : δ ≤ r0 / 2 := min_le_right _ _
  have hwin : Set.Ioo (r0 - δ) r0 ∈ 𝓝[<] r0 := Ioo_mem_nhdsLT (by linarith)
  have hfac : ∀ᶠ r : ℝ in 𝓝[<] r0, ∀ e : Sym2 M.V,
      M.cutPivotFactor r e = M.cutPivotFactorLT r0 e := by
    filter_upwards [hwin] with r hr e
    exact M.cutPivotFactor_eq_LT_of_left_window (r0 := r0) (ε := ε) hε
      (by linarith [hr.1, hδε]) hr.2 e
  have hrlt : ∀ᶠ r : ℝ in 𝓝[<] r0, r < R ∧ 0 < r := by
    filter_upwards [hwin] with r hr
    exact ⟨by linarith [hr.2, hr0R], by linarith [hr.1, hδr]⟩
  have hsumm : Summable (M.pivotMajorant r0 R) := M.summable_pivotMajorant h1
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] r0, ∀ e : Sym2 M.V,
      ‖M.cutPivotFactorLT r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖
        ≤ M.pivotMajorant r0 R e := by
    filter_upwards [hrlt] with r hr
    intro e
    have hpivnonneg : 0 ≤ pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω
    have hnn : 0 ≤ M.cutPivotFactorLT r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e :=
      mul_nonneg (M.cutPivotFactorLT_nonneg r0 e) hpivnonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc M.cutPivotFactorLT r0 e * pivotalFlux (edgeMeasure (M.cutProb r))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
        ≤ M.cutPivotFactorLT r0 e * M.edgeTouchMass r e :=
          mul_le_mul_of_nonneg_left (M.pivotalFlux_singleton_le_edgeTouchMass y e)
            (M.cutPivotFactorLT_nonneg r0 e)
      _ ≤ M.cutPivotFactorLT r0 e * M.edgeTouchMass R e :=
          mul_le_mul_of_nonneg_left (M.edgeTouchMass_mono hr.2 (lt_trans hr0 hr0R) hr.1.le e)
            (M.cutPivotFactorLT_nonneg r0 e)
      _ ≤ M.cutPivotFactor r0 e * M.edgeTouchMass R e :=
          mul_le_mul_of_nonneg_right (M.cutPivotFactorLT_le r0 e) (M.edgeTouchMass_nonneg R e)
      _ = M.pivotMajorant r0 R e := rfl
  have htend : Tendsto (fun r => ∑' e : Sym2 M.V, M.cutPivotFactorLT r0 e *
      pivotalFlux (edgeMeasure (M.cutProb r))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) (𝓝[<] r0)
      (𝓝 (∑' e : Sym2 M.V, M.cutPivotFactorLT r0 e *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := M.pivotMajorant r0 R) hsumm ?_ hbound
    intro e
    by_cases hs : inSupport M r0 e
    · exact ((M.continuousAt_pivotalFlux_singleton hr0 hr0R hfin y e).tendsto.mono_left
        nhdsWithin_le_nhds).const_mul (M.cutPivotFactorLT r0 e)
    · have hzero : M.cutPivotFactor r0 e = 0 := M.cutPivotFactor_eq_zero_of_not_inSupport r0 hs
      have hLT : M.cutPivotFactorLT r0 e = 0 :=
        le_antisymm (hzero ▸ M.cutPivotFactorLT_le r0 e) (M.cutPivotFactorLT_nonneg r0 e)
      simp only [hLT, zero_mul]
      exact tendsto_const_nhds
  refine htend.congr' ?_
  filter_upwards [hfac] with r hr
  rw [normalizedPivotMass]
  exact tsum_congr fun e => by rw [hr e]


/-! ## 5. The activation shell and the continuity criterion -/

/-- The normalized pivotal summand at a fixed radius is summable under a finite first moment at
a strictly larger radius. -/
theorem summable_normalizedPivotSummand {y : M.V} {r0 R : ℝ}
    (hr0 : 0 < r0) (hr0R : r0 < R) (h1 : M.cutMoment 1 R ≠ ⊤) :
    Summable (fun e : Sym2 M.V => M.cutPivotFactor r0 e *
      pivotalFlux (edgeMeasure (M.cutProb r0))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) := by
  refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_)
    (M.summable_pivotMajorant (r0 := r0) (R := R) h1)
  · exact mul_nonneg (M.cutPivotFactor_nonneg r0 e) (by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω)
  · have hpiv : pivotalFlux (edgeMeasure (M.cutProb r0))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
        ≤ M.edgeTouchMass R e :=
      (M.pivotalFlux_singleton_le_edgeTouchMass y e).trans
        (M.edgeTouchMass_mono hr0 (hr0.trans hr0R) hr0R.le e)
    exact mul_le_mul_of_nonneg_left hpiv (M.cutPivotFactor_nonneg r0 e)

/-- The left-hand summand is summable. -/
theorem summable_normalizedPivotSummandLT {y : M.V} {r0 R : ℝ}
    (hr0 : 0 < r0) (hr0R : r0 < R) (h1 : M.cutMoment 1 R ≠ ⊤) :
    Summable (fun e : Sym2 M.V => M.cutPivotFactorLT r0 e *
      pivotalFlux (edgeMeasure (M.cutProb r0))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) :=
  Summable.of_nonneg_of_le
    (fun e => mul_nonneg (M.cutPivotFactorLT_nonneg r0 e) (by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω))
    (fun e => mul_le_mul_of_nonneg_right (M.cutPivotFactorLT_le r0 e) (by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω))
    (M.summable_normalizedPivotSummand (y := y) hr0 hr0R h1)

/-- The activation shell at `r0` (the summands that appear when `r` crosses `r0`) is
summable. -/
theorem summable_activationShell {y : M.V} {r0 R : ℝ}
    (hr0 : 0 < r0) (hr0R : r0 < R) (h1 : M.cutMoment 1 R ≠ ⊤) :
    Summable (fun e : Sym2 M.V => (M.cutPivotFactor r0 e - M.cutPivotFactorLT r0 e) *
      pivotalFlux (edgeMeasure (M.cutProb r0))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) := by
  refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_)
    (M.summable_normalizedPivotSummand (y := y) hr0 hr0R h1)
  · exact mul_nonneg (sub_nonneg.mpr (M.cutPivotFactorLT_le r0 e)) (by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω)
  · exact mul_le_mul_of_nonneg_right (sub_le_self _ (M.cutPivotFactorLT_nonneg r0 e)) (by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω)

/-- **The value at `r0` is the left limit plus the activation shell.** -/
theorem normalizedPivotMass_eq_leftLimit_add_shell {y : M.V} {r0 R : ℝ}
    (hr0 : 0 < r0) (hr0R : r0 < R) (h1 : M.cutMoment 1 R ≠ ⊤) :
    M.normalizedPivotMass y r0 =
      (∑' e : Sym2 M.V, M.cutPivotFactorLT r0 e *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)
      + ∑' e : Sym2 M.V, (M.cutPivotFactor r0 e - M.cutPivotFactorLT r0 e) *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
  rw [normalizedPivotMass]
  have hcongr : (fun e : Sym2 M.V => M.cutPivotFactor r0 e *
      pivotalFlux (edgeMeasure (M.cutProb r0))
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)
      = fun e : Sym2 M.V => (M.cutPivotFactorLT r0 e *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)
        + (M.cutPivotFactor r0 e - M.cutPivotFactorLT r0 e) *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
    funext e
    ring
  rw [hcongr, Summable.tsum_add
    (M.summable_normalizedPivotSummandLT (y := y) hr0 hr0R h1)
    (M.summable_activationShell (y := y) hr0 hr0R h1)]

/-- **Continuity at a positive radius is exactly the vanishing of the activation shell.** -/
theorem continuousAt_iff_activationShell_eq_zero {y : M.V} {r0 R : ℝ}
    (hr0 : 0 < r0) (hr0R : r0 < R) (h1 : M.cutMoment 1 R ≠ ⊤) :
    ContinuousAt (M.normalizedPivotMass y) r0 ↔
      (∑' e : Sym2 M.V, (M.cutPivotFactor r0 e - M.cutPivotFactorLT r0 e) *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) = 0 := by
  constructor
  · intro hcont
    have hleft : Tendsto (M.normalizedPivotMass y) (𝓝[<] r0)
        (𝓝 (M.normalizedPivotMass y r0)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hlim := M.tendsto_normalizedPivotMass_nhdsLT_trimmed (y := y) hr0 hr0R h1
    have heq : (∑' e : Sym2 M.V, M.cutPivotFactorLT r0 e *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)
        = M.normalizedPivotMass y r0 := tendsto_nhds_unique hlim hleft
    have hsplit := M.normalizedPivotMass_eq_leftLimit_add_shell (y := y) hr0 hr0R h1
    linarith
  · intro hshell
    have hlim := M.tendsto_normalizedPivotMass_nhdsLT_trimmed (y := y) hr0 hr0R h1
    have hsplit := M.normalizedPivotMass_eq_leftLimit_add_shell (y := y) hr0 hr0R h1
    have heq : (∑' e : Sym2 M.V, M.cutPivotFactorLT r0 e *
        pivotalFlux (edgeMeasure (M.cutProb r0))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) =
        M.normalizedPivotMass y r0 := by
      rw [hsplit, hshell, add_zero]
    have hleft : Tendsto (M.normalizedPivotMass y) (𝓝[<] r0)
        (𝓝 (M.normalizedPivotMass y r0)) := by
      simpa only [heq] using hlim
    have hright := M.tendsto_normalizedPivotMass_nhdsGT (y := y) hr0 hr0R h1
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hspec₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim ε hε
    obtain ⟨δ₂, hδ₂, hspec₂⟩ := Metric.tendsto_nhdsWithin_nhds.mp hright ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx => ?_⟩
    rw [Real.dist_eq] at hx
    rcases lt_trichotomy x r0 with h | h | h
    · have hb := hspec₁ h (by
        rw [Real.dist_eq]
        exact lt_of_lt_of_le hx (min_le_left _ _))
      rw [heq] at hb
      exact hb
    · subst h
      simpa using hε
    · exact hspec₂ h (by
        rw [Real.dist_eq]
        exact lt_of_lt_of_le hx (min_le_right _ _))

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 6. Axiom audit -/

open PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutPivotFactor_mono_r
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutPivotFactor_eq_of_right_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutPivotFactor_eq_LT_of_left_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_normalizedPivotMass_nhdsGT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_normalizedPivotMass_nhdsLT_trimmed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.normalizedPivotMass_eq_leftLimit_add_shell
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_iff_activationShell_eq_zero
