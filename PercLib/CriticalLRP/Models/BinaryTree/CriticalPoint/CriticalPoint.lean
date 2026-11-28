/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m7.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m7/src/M7BinaryTree.lean`.
-/

module

public import PercLib.Models.BinaryTree.Subcritical.Basic

/-!
# The binary-tree critical parameter is exactly `log 2`, and the critical mean diverges

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, p. 6
(`β_c := inf{β ≥ 0 : an infinite cluster exists P_β-a.s.}`) and p. 35
("Since `E_{β_c}|K| = ∞`").

`Models/BinaryTree/Subcritical/Basic.lean` records that "`β_c = log 2` is one structural
step away".  This file takes that step and draws the consequences.  The kernel is the
nonzero `binaryTreeKernel` on `List (Fin 2)` (open probability `1 - e^{-β}` on tree edges,
`0` elsewhere), and everything is stated in the paper's own
`longRangeMeasure J hJ β` / `criticalBeta J hJ` interface.

* `criticalBeta_binaryTreeKernel_eq_logTwo` : `β_c = log 2`.
* `percolationFunction_binaryTreeKernel_eq_zero_of_pos_of_treeProb_le` : below the
  threshold every root fails to percolate, not only the root `[]` — the passage from one
  root to all roots uses `law_cluster_infinite_pos_iff_of_preconnected`.
* `lintegral_clusterVol_binaryTreeKernel_criticalBeta_eq_top` : `E_{β_c}|K_[]| = ⊤`, an
  attained instance of the source's asserted input with `β_c = log 2 > 0`.
* `percolationFunction_binaryTreeKernel_criticalBeta_eq_zero` : `θ_{β_c} ≡ 0`, so `θ = 0`
  and an infinite mean coexist at `β_c`.
* `lintegral_clusterVol_binaryTreeKernel_lt_top_iff_lt_criticalBeta` : the finite-mean set
  is exactly `[0, β_c)`, i.e. the mean threshold equals the percolation threshold.
* `criticalBetaSet_binaryTreeKernel_eq_Ioi` : the percolating set is exactly `(β_c, ∞)`.

Not claimed: anything about the power-law kernels of the paper on `ℤ^d`.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond
open scoped ENNReal

namespace PercLib.CriticalLRP

theorem zero_lt_logTwo : (0 : NNReal) < logTwo := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_zero, logTwo_coe]
  exact Real.log_pos one_lt_two

theorem criticalBetaSet_binaryTreeKernel_nonempty :
    (criticalBetaSet binaryTreeKernel binaryTreeKernel_nonneg).Nonempty :=
  ⟨logTwo + 1, mem_criticalBetaSet_binaryTreeKernel _ (by
    rw [half_lt_treeProb_coe_iff]
    exact lt_add_of_pos_right _ zero_lt_one)⟩

theorem percolationFunction_binaryTreeKernel_eq_zero_of_pos_of_treeProb_le
    (β : NNReal) (hpos : 0 < β) (hp : ((treeProb β : unitInterval) : ℝ) ≤ 1 / 2)
    (v : List (Fin 2)) :
    percolationFunction binaryTreeKernel binaryTreeKernel_nonneg β v = 0 := by
  have hpre := binaryTree_support_preconnected β hpos
  have hroot : law (bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β)
      {ω : Config (List (Fin 2)) | (cluster ω ([] : List (Fin 2))).Infinite} = 0 := by
    rw [← percolationFunction_eq_law_cluster_infinite,
      percolationFunction_binaryTreeKernel_eq_zero β hp]
  have hiff := PercLib.Percolation.Bond.law_cluster_infinite_pos_iff_of_preconnected
    (bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β) hpre v []
  rw [percolationFunction_eq_law_cluster_infinite]
  have hnot : ¬ (0 : ℝ≥0∞) < law (bernoulliEdgeProb binaryTreeKernel binaryTreeKernel_nonneg β)
      {ω : Config (List (Fin 2)) | (cluster ω v).Infinite} := by
    rw [hiff, hroot]
    exact lt_irrefl 0
  exact le_bot_iff.mp (not_lt.mp hnot)

theorem infiniteClusterProb_binaryTreeKernel_eq_zero_of_pos_of_lt_logTwo
    (β : NNReal) (hpos : 0 < β) (hβ : β < logTwo) :
    infiniteClusterProb binaryTreeKernel binaryTreeKernel_nonneg β = 0 := by
  rw [infiniteClusterProb_eq_zero_iff_forall binaryTreeKernel_nonneg]
  exact percolationFunction_binaryTreeKernel_eq_zero_of_pos_of_treeProb_le β hpos
    (le_of_lt ((treeProb_coe_lt_half_iff β).2 hβ))

theorem criticalBeta_binaryTreeKernel_ge_logTwo :
    logTwo ≤ criticalBeta binaryTreeKernel binaryTreeKernel_nonneg := by
  by_contra h
  push Not at h
  obtain ⟨γ, h1, h2⟩ := exists_between h
  have hmem : γ ∈ criticalBetaSet binaryTreeKernel binaryTreeKernel_nonneg :=
    mem_of_criticalBeta_lt criticalBetaSet_binaryTreeKernel_nonempty h1
  rw [mem_criticalBetaSet_iff] at hmem
  have hzero := infiniteClusterProb_binaryTreeKernel_eq_zero_of_pos_of_lt_logTwo γ
    (lt_trans criticalBeta_binaryTreeKernel_pos h1) h2
  rw [hzero] at hmem
  exact zero_ne_one hmem

theorem criticalBeta_binaryTreeKernel_eq_logTwo :
    criticalBeta binaryTreeKernel binaryTreeKernel_nonneg = logTwo :=
  le_antisymm criticalBeta_binaryTreeKernel_le_logTwo criticalBeta_binaryTreeKernel_ge_logTwo

theorem infiniteClusterProb_binaryTreeKernel_criticalBeta_eq_zero :
    infiniteClusterProb binaryTreeKernel binaryTreeKernel_nonneg
      (criticalBeta binaryTreeKernel binaryTreeKernel_nonneg) = 0 := by
  rw [criticalBeta_binaryTreeKernel_eq_logTwo,
    infiniteClusterProb_eq_zero_iff_forall binaryTreeKernel_nonneg]
  exact percolationFunction_binaryTreeKernel_eq_zero_of_pos_of_treeProb_le logTwo
    zero_lt_logTwo (le_of_eq treeProb_coe_logTwo)

theorem percolationFunction_binaryTreeKernel_criticalBeta_eq_zero (v : List (Fin 2)) :
    percolationFunction binaryTreeKernel binaryTreeKernel_nonneg
      (criticalBeta binaryTreeKernel binaryTreeKernel_nonneg) v = 0 :=
  (infiniteClusterProb_eq_zero_iff_forall binaryTreeKernel_nonneg).1
    infiniteClusterProb_binaryTreeKernel_criticalBeta_eq_zero v

theorem lintegral_clusterVol_binaryTreeKernel_criticalBeta_eq_top :
    ∫⁻ ω, clusterVol ω ([] : List (Fin 2))
        ∂longRangeMeasure binaryTreeKernel binaryTreeKernel_nonneg
          (criticalBeta binaryTreeKernel binaryTreeKernel_nonneg) = ⊤ := by
  refine lintegral_clusterVol_binaryTreeKernel_eq_top _ ?_
  rw [criticalBeta_binaryTreeKernel_eq_logTwo]
  exact le_of_eq treeProb_coe_logTwo.symm

theorem lintegral_clusterVol_binaryTreeKernel_lt_top_iff_lt_criticalBeta (β : NNReal) :
    ∫⁻ ω, clusterVol ω ([] : List (Fin 2))
        ∂longRangeMeasure binaryTreeKernel binaryTreeKernel_nonneg β < ⊤ ↔
      β < criticalBeta binaryTreeKernel binaryTreeKernel_nonneg := by
  rw [criticalBeta_binaryTreeKernel_eq_logTwo]
  exact lintegral_clusterVol_binaryTreeKernel_lt_top_iff β

theorem criticalBetaSet_binaryTreeKernel_eq_Ioi :
    criticalBetaSet binaryTreeKernel binaryTreeKernel_nonneg =
      Set.Ioi (criticalBeta binaryTreeKernel binaryTreeKernel_nonneg) := by
  ext β
  constructor
  · intro hβ
    rw [Set.mem_Ioi]
    refine lt_of_le_of_ne (criticalBeta_le_of_mem hβ) ?_
    rintro rfl
    rw [mem_criticalBetaSet_iff] at hβ
    rw [infiniteClusterProb_binaryTreeKernel_criticalBeta_eq_zero] at hβ
    exact zero_ne_one hβ
  · intro hβ
    exact mem_of_criticalBeta_lt criticalBetaSet_binaryTreeKernel_nonempty hβ

end PercLib.CriticalLRP

section AxiomAudit
open PercLib.CriticalLRP
#print axioms PercLib.CriticalLRP.criticalBeta_binaryTreeKernel_eq_logTwo
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_binaryTreeKernel_criticalBeta_eq_top
#print axioms PercLib.CriticalLRP.percolationFunction_binaryTreeKernel_criticalBeta_eq_zero
#print axioms PercLib.CriticalLRP.lintegral_clusterVol_binaryTreeKernel_lt_top_iff_lt_criticalBeta
#print axioms PercLib.CriticalLRP.criticalBetaSet_binaryTreeKernel_eq_Ioi
end AxiomAudit
