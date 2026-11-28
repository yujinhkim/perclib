/-
Ultramath swarm `smwzqts7r`, member `m8`, direction `d3`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m8.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m8/Defs.lean`.

# Source-fidelity audit at production HEAD `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`

Independent, kernel-checked statements supporting the audit of the integrated
Case-1 / Case-2 / Case-3HD / Case-3HDLarge / HDClosure / CornerContinuity /
CriticalVolumeTail-UniformCutoff packages against Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1.

This module imports the earlier production results and independently re-derives
or checks specific points from the printed source.

* §1 constants and admissible range of Lemma I.4.16 (p. 43), at `(p,k) = (6,2)` and `(4,1)`;
* §2 `CaseTwo.SixthMomentMixed` is *exactly* the printed instance and it has content;
* §3 the normalisation of `I16rhs` (used by the frozen Theorem I.1.6 anchor, p. 10) is *not*
  the `A` of Proposition I.4.15 (p. 43); the two are related by `A_{I.1.6} = A_{I.4.15} / (α/β_c)`,
  so a consumer must not identify them;
* §4 the literal (HD)(3) forces `1 < ‖x − y‖` at every pair with positive connection probability
  (re-derived independently of `HDClosure`'s own proof);
* §5 the cited uncut volume-tail leaf `CriticalVolumeTail C` forces `C ≥ 1` (and so does the
  radius-uniform cutoff form): the leaf is not vacuous and cannot be weakened to `C = 0`;
* §6 the Case-2 exponent `(9α − 3d)/4` is the paper's (I.4.18) exponent `2α − d + (d+α)/4`;
* §7 interface check: `CriticalVolumeTail` produces exactly the `hgm` hypothesis that the
  Case-3 assemblers retain (with the source's constant `(4C+1)^{-3}`).
-/
module
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.UniformCutoff.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.LargeDistance.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase2.Source.Defs

/-! Kernel-checked normalization and interface facts for the source-fidelity review. -/

set_option linter.hashCommand false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped ENNReal NNReal Topology
open MeasureTheory Filter
open PercLib.CriticalLRP Orchestration

@[expose] public section

namespace Audit

/-! ### §1 Constants of Lemma I.4.16 -/

theorem M_five_eq : VolumeMoments.M 5 = 945 := by decide
theorem M_one_eq : VolumeMoments.M 1 = 1 := by decide
theorem M_two_eq : VolumeMoments.M 2 = 3 := by decide

theorem lemma_I416_exp_p6_k2 : 2 * (6:ℝ) - 1 - 3 * (2:ℝ) = 5 := by norm_num
theorem lemma_I416_exp_p4_k1 : 2 * (4:ℝ) - 1 - 3 * (1:ℝ) = 4 := by norm_num
/-- `k = 2` is inside the admissible range `0 ≤ k ≤ ⌈(p-1)/2⌉ = 3` at `p = 6`. -/
theorem lemma_I416_k_admissible_p6 : 2 ≤ (6 + 1) / 2 := by norm_num
theorem lemma_I416_k_admissible_p4 : 1 ≤ (4 + 1) / 2 := by norm_num

/-! ### §2 `SixthMomentMixed` is exactly the printed instance, and it has content -/

theorem sixthMomentMixed_apply (M : SourceModelData) (h : CaseTwo.SixthMomentMixed M)
    {r : ℝ} (hr : 0 ≤ r) :
    M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5 :=
  h r hr

theorem sixthMomentMixed_cutMoment_six_ne_top (M : SourceModelData) (h : CaseTwo.SixthMomentMixed M)
    {r : ℝ} (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤) : M.cutMoment 6 r ≠ ⊤ := by
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  refine ne_top_of_le_ne_top ?_ (h r hr)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top h2))
    (ENNReal.pow_ne_top h1)

/-! ### §3 Normalisation: Theorem I.1.6's `A` versus Proposition I.4.15's `A` -/

/-- The `(2p−1)α` growth with the *Proposition I.4.20* normalisation
`(2p−3)!! A^{p−1} (α/β_c)^{2−p} r^{(2p−1)α}`, written with `c^{2−p} = c / c^{p−1}`. -/
noncomputable def I16rhsProp420 (M : SourceModelData) (A : ℝ) (p : ℕ) (r : ℝ) : ℝ :=
  (VolumeMoments.M (p - 1) : ℝ) * A ^ (p - 1)
    * ((M.α / (M.betaCrit : ℝ)) / (M.α / (M.betaCrit : ℝ)) ^ (p - 1))
    * r ^ ((2 * (p : ℝ) - 1) * M.α)

theorem I16rhs_eq_scaled (M : SourceModelData) (A : ℝ) (p : ℕ) (r : ℝ)
    (hκ : M.α / (M.betaCrit : ℝ) ≠ 0) :
    I16rhs M A p r = I16rhsProp420 M (A * (M.α / (M.betaCrit : ℝ))) p r := by
  simp only [I16rhs, I16rhsProp420, mul_pow]
  field_simp

theorem I16rhs_one (M : SourceModelData) (A : ℝ) (r : ℝ) :
    I16rhs M A 1 r = (M.α / (M.betaCrit : ℝ)) * r ^ ((2 * (1:ℝ) - 1) * M.α) := by
  simp [I16rhs, VolumeMoments.M]

theorem I16rhs_two (M : SourceModelData) (A : ℝ) (r : ℝ) :
    I16rhs M A 2 r = A * (M.α / (M.betaCrit : ℝ)) * r ^ ((2 * (2:ℝ) - 1) * M.α) := by
  simp [I16rhs, VolumeMoments.M]

/-! ### §4 The short-distance constraint of the literal (HD)(3) -/

theorem case3HD_one_lt_dist (M : SourceModelData) (h : M.Case3HD)
    {x y : M.V} (hxy : x ≠ y) (hpos : 0 < M.twoPoint M.betaCrit x y) :
    1 < M.S.dist x y := by
  by_contra hle
  have hle' : M.S.dist x y ≤ 1 := not_lt.mp hle
  obtain ⟨C, hC, hb⟩ := h.2.2
  have hdpos : 0 < M.S.dist x y := M.S.dist_pos hxy
  have hlog : Real.log (M.S.dist x y) ≤ 0 := Real.log_nonpos hdpos.le hle'
  have hinv : (Real.log (M.S.dist x y))⁻¹ ≤ 0 := by
    rcases lt_or_eq_of_le hlog with hlt | heq
    · exact le_of_lt (inv_neg''.mpr hlt)
    · rw [heq, inv_zero]
  have hpow : 0 < (M.S.dist x y) ^ (-(M.d : ℝ) + 2) := Real.rpow_pos_of_pos hdpos _
  have hnonpos : C * (Real.log (M.S.dist x y))⁻¹ * (M.S.dist x y) ^ (-(M.d : ℝ) + 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hC.le hinv) hpow.le
  have hb' : M.twoPoint M.betaCrit x y
      ≤ C * (Real.log (M.S.dist x y))⁻¹ * (M.S.dist x y) ^ (-(M.d : ℝ) + 2) := hb x y hxy
  linarith

/-! ### §5 The cited uncut volume-tail leaf has content -/

theorem criticalVolumeTail_one_le (M : SourceModelData) {C : ℝ}
    (h : M.CriticalVolumeTail C) : 1 ≤ C := by
  haveI : IsProbabilityMeasure M.criticalLaw :=
    inferInstanceAs (IsProbabilityMeasure
      (longRangeMeasure M.kernel M.kernel_nonneg M.betaCrit))
  have hev : {ω : Config M.V | ((1 : ℕ) : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    simpa using SourceModelData.one_le_clusterVol ω (0 : M.V)
  have h1 : M.criticalLaw {ω : Config M.V | ((1 : ℕ) : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} = 1 := by
    rw [hev, measure_univ]
  have h2 := h 1 le_rfl
  rw [h1] at h2
  simp only [Analysis.Route3.tailEnvelope, Nat.cast_one, Real.sqrt_one, div_one] at h2
  by_contra hcon
  by_cases hlt : C < 0
  · rw [ENNReal.ofReal_eq_zero.mpr hlt.le] at h2
    exact absurd h2 (not_le.mpr one_pos)
  · have hle : 0 ≤ C := not_lt.mp hlt
    have h3 : ((1 : ℝ≥0∞)).toReal ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rw [ENNReal.toReal_ofReal hle, ENNReal.toReal_one] at h3
    exact hcon h3

/-! ### §6 The Case-2 exponent is the paper's (I.4.18) -/

theorem caseTwo_exponent_identity (α d : ℝ) :
    2 * α - d + (d + α) / 4 = (9 * α - 3 * d) / 4 := by ring

end Audit

namespace Audit

/-! ### §7 Interface check: `hgm` of the Case-3 assemblers is exactly the tail's output -/

theorem hgm_of_volumeTail (M : SourceModelData) {C : ℝ} (hC : 0 ≤ C)
    (hTail : M.CriticalVolumeTail C)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal := by
  refine ⟨(Analysis.Route3.ratioConst C)⁻¹,
    inv_pos.mpr (Analysis.Route3.ratioConst_pos hC), ?_⟩
  filter_upwards [h2, eventually_gt_atTop (0 : ℝ)] with r h2r hr
  exact M.momentGap_of_volumeTail hC hTail hr h2r

theorem uniformCutTail_one_le (M : SourceModelData) {C : ℝ}
    (h : ∀ r : ℝ, 0 < r → ∀ n : ℕ, 1 ≤ n →
      M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
        ≤ Analysis.Route3.tailEnvelope C n) : 1 ≤ C := by
  haveI : IsProbabilityMeasure (M.cutLaw 1) := inferInstance
  have hev : {ω : Config M.V | ((1 : ℕ) : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    simpa using SourceModelData.one_le_clusterVol ω (0 : M.V)
  have h2 := h 1 one_pos 1 le_rfl
  rw [hev, measure_univ] at h2
  simp only [Analysis.Route3.tailEnvelope, Nat.cast_one, Real.sqrt_one, div_one] at h2
  by_contra hcon
  by_cases hlt : C < 0
  · rw [ENNReal.ofReal_eq_zero.mpr hlt.le] at h2
    exact absurd h2 (not_le.mpr one_pos)
  · have hle : 0 ≤ C := not_lt.mp hlt
    have h3 : ((1 : ℝ≥0∞)).toReal ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rw [ENNReal.toReal_ofReal hle, ENNReal.toReal_one] at h3
    exact hcon h3

/-! ### §8 Axiom audit of this file -/

#print axioms Audit.M_five_eq
#print axioms Audit.lemma_I416_exp_p6_k2
#print axioms Audit.sixthMomentMixed_cutMoment_six_ne_top
#print axioms Audit.I16rhs_eq_scaled
#print axioms Audit.I16rhs_two
#print axioms Audit.case3HD_one_lt_dist
#print axioms Audit.criticalVolumeTail_one_le
#print axioms Audit.caseTwo_exponent_identity
#print axioms Audit.hgm_of_volumeTail
#print axioms Audit.uniformCutTail_one_le

end Audit
