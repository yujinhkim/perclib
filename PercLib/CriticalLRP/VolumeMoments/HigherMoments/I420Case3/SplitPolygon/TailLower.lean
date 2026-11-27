/- Integrated from `.scratch/case3-split-draft/TailLower.lean` at production base
`00def8972103ffee4166a7285ded1c111a387607`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.MomentHom
public import PercLib.CriticalLRP.Analysis.Route3.Percolation
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffMomentContinuity

/-! # The lower second-moment comparison from the critical volume tail -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

set_option linter.hashCommand false
set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration
open Analysis.Route3

/-- The real shadow of a canonical cutoff cluster moment is exactly the source
`cutMoment` at the same order. -/
theorem momOf_cutProb_eq_toReal_cutMoment (M : SourceModelData) (r : ℝ) (m : ℕ) :
    momOf (fun r => M.cutProb r) (0 : M.V) m r = (M.cutMoment m r).toReal := rfl

/-- Proposition I.4.15's lower comparison for the direct Case-3 assembler. The
only probabilistic inputs are the uncut critical $n^{-1/2}$ volume-tail bound and
finiteness of the cutoff second moment. -/
theorem case3_hgm_of_tail (M : SourceModelData) {C : ℝ} (hC : 0 ≤ C)
    (hTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        tailEnvelope C n)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ᶠ r in atTop,
      c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
        ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r := by
  refine ⟨(ratioConst C)⁻¹, inv_pos.mpr (ratioConst_pos hC), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  have hbase := Orchestration.cutMoment_one_cube_le_two_of_tail M hC hrpos hTail
  have h2fin := h2 r hr
  have h1fin : M.cutMoment 1 r ≠ ⊤ := by
    rw [M.cutMoment_one_eq_cutMassAt]
    exact ne_top_of_le_ne_top h2fin (E1Sign.cutMassAt_le_cutMoment_two M r)
  have hreal : (M.cutMoment 1 r).toReal ^ 3 ≤ ratioConst C * (M.cutMoment 2 r).toReal := by
    have h := (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top h1fin)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2fin)).mpr hbase
    simpa only [ENNReal.toReal_pow, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (ratioConst_nonneg hC)] using h
  rw [momOf_cutProb_eq_toReal_cutMoment M r 1, momOf_cutProb_eq_toReal_cutMoment M r 2]
  calc (ratioConst C)⁻¹ * (M.cutMoment 1 r).toReal ^ 3
      ≤ (ratioConst C)⁻¹ * (ratioConst C * (M.cutMoment 2 r).toReal) := by
        exact mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr (ratioConst_nonneg hC))
    _ = (M.cutMoment 2 r).toReal := by
        rw [← mul_assoc, inv_mul_cancel₀ (ratioConst_ne_zero hC), one_mul]

#print axioms momOf_cutProb_eq_toReal_cutMoment
#print axioms case3_hgm_of_tail

end I420Case3

end PercLib.CriticalLRP
