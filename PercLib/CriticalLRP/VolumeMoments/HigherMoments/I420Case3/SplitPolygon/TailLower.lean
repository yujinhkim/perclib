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

/-- The normalized cutoff error with the second-moment lower comparison derived
from the critical volume tail. `hTail` is the base open-triangle-tail decay;
`hVolTail` is the separate uncut volume-tail envelope. Their roles are kept
explicit rather than conflated. -/
theorem exists_case3_i421_cutPoly_source_of_tail (M : SourceModelData)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p) (hℓ : ℓ + 1 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hVolTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        tailEnvelope C n)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hmom : ∀ r : ℝ, 1 ≤ r → ∀ m : ℕ, 1 ≤ m → m ≤ p + 1 →
      I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤) :
    ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) := by
  obtain ⟨c3, hc3, hgm⟩ := case3_hgm_of_tail M hC hVolTail h2
  have hMa : ∀ r : ℝ, 1 ≤ r → I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤ :=
    fun r hr => hmom r hr (ℓ + 1) (by omega) (by omega)
  have hMb : ∀ (r : ℝ), 1 ≤ r → ∀ y ∈ (BallAverage.ball_finite M r).toFinset,
      I420Case1.powMomentAt (M.cutProb r) (p - ℓ) y ≠ ⊤ := by
    intro r hr y _
    rw [powMomentAt_cutProb_apply_eq_zero M r (p - ℓ) y]
    have hidx : p - ℓ - 1 + 1 = p - ℓ := by omega
    rw [← hidx]
    exact hmom r hr (p - ℓ - 1 + 1) (by omega) (by omega)
  exact exists_case3_i421_cutPoly_source M hP hTri 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1
    hTail hMa hMb hc3 hgm

#print axioms momOf_cutProb_eq_toReal_cutMoment
#print axioms case3_hgm_of_tail
#print axioms exists_case3_i421_cutPoly_source_of_tail

end I420Case3

end PercLib.CriticalLRP
