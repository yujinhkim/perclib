/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

Ultramath swarm `smwziumdb`, member `m2`, direction `d5`.

# The Case-3 window numerator is the sum of the per-vertex product gaps

The abstract per-vertex objects of `Defs.lean` are here identified with the source model's own
quantities (`M.connCubeVertexMass`, `M.exclMassQuad`, `M.cutMoment`), and the Case-3 numerator of
display (I.4.16),

  `|B_r| E_{β_c,r}|K| E_{β_c,r}|K|² − E_{β_c,r}[|K| ∑_{y∈B_r} 1(y∉K)|K_y|²]`,

is proved to be the finite window sum of the per-vertex `(1,2)` product gaps.  This is the exact
form in which a per-vertex bound on `gapVert` (e.g. the `(2,1)` interface
`I417.I417_p21_source_tsub_le_excess` instantiated at the reversed pair `(y,0)`) enters the
Case-3 consumer: no `|B_r|`-loss, no star substitution.

`connCubeMass_eq_sum_starVert` and `windowNumerator_le_connCubeMass` record the two-sided
relation with the star: the numerator is at most the star window mass (this is the trivial half of
(I.4.16)), and the difference is the window covariance (`Main.lean`,
`starVert_toReal_eq_gapVert_add_covVert`).
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Main

/-! # Independently reviewed Case-3 repair-audit module: Model -/


noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP
namespace QZeroRepairAudit

attribute [local instance] Classical.propDecidable

open Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The star and the excluded moment in the model's notation -/

/-- `starVert` at `p = 3`, basepoint `0`, is the source's per-vertex numerator
`E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` (`M.connCubeVertexMass`). -/
theorem starVert_cutProb_eq_connCubeVertexMass (r : ℝ) (y : M.V) :
    starVert (M.cutProb r) (0 : M.V) y 3 = M.connCubeVertexMass r y := by
  rw [starVert, SourceModelData.connCubeVertexMass, M.cutLaw_eq_edgeMeasure]

/-- The star window mass is the sum of the per-vertex star moments
(production's `connCubeMass_eq_sum_vertex`, restated in the audit's notation). -/
theorem connCubeMass_eq_sum_starVert (r : ℝ) :
    M.connCubeMass r = ∑ y ∈ E1Sign.ballF M r, starVert (M.cutProb r) (0 : M.V) y 3 := by
  rw [M.connCubeMass_eq_sum_vertex r]
  exact Finset.sum_congr rfl fun y _ => (starVert_cutProb_eq_connCubeVertexMass M r y).symm

/-- The excluded window mass is the sum of the per-vertex excluded moments
`E[1(y ∉ K_0)|K_0||K_y|²]`. -/
theorem exclMassQuad_eq_sum_exclVert (r : ℝ) :
    M.exclMassQuad r
      = ∑ y ∈ E1Sign.ballF M r, exclVert (M.cutProb r) (0 : M.V) y 1 2 := by
  rw [M.exclMassQuad_eq_sum_single]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [exclVert, M.cutLaw_eq_edgeMeasure, pow_one]

/-- The product factor `E|K_0| · E|K|²`, summed over the window, is `|B_r| χ χ₂`: this is the
product term of the Case-3 numerator. -/
theorem sum_prodVert_cutProb (r : ℝ) :
    ∑ y ∈ E1Sign.ballF M r, prodVert (M.cutProb r) (0 : M.V) y 1 2
      = ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r := by
  have hterm : ∀ y ∈ E1Sign.ballF M r,
      prodVert (M.cutProb r) (0 : M.V) y 1 2 = M.cutMoment 1 r * M.cutMoment 2 r := by
    intro y _
    rw [prodVert, M.powMomentAt_cutProb_eq_cutMoment, M.powMomentAt_cutProb_eq_cutMoment]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, E1Sign.card_ballF M r, nsmul_eq_mul]
  ring

/-! ## 2. The window numerator is the sum of the per-vertex product gaps -/

/-- **The real-valued Case-3 numerator of (I.4.16) is the window sum of the per-vertex `(1,2)`
product gaps.**

Every summand is `prodVert − exclVert = gapVert`, the excluded sum is exactly `M.exclMassQuad r`
(finite Tonelli, production's `exclMassQuad_eq_sum_single`), and the product sum is `|B_r| χ χ₂`.
The subtraction is carried out in `ℝ` with the finiteness of `E|K|²` making the conversion
faithful; there is no `⊤ ↦ 0` step. -/
theorem windowNumerator_toReal_eq_sum_gapVert_toReal (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r
        - M.exclMassQuad r).toReal
      = ∑ y ∈ E1Sign.ballF M r, (gapVert (M.cutProb r) (0 : M.V) y 1 2).toReal := by
  classical
  let := Encodable.ofCountable (Sym2 M.V)
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have htop : ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) h1) h2
  have hle : M.exclMassQuad r ≤ ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r :=
    M.exclMassQuad_le_ball_mul_moments r
  have hexcl : ∀ y ∈ E1Sign.ballF M r,
      exclVert (M.cutProb r) (0 : M.V) y 1 2
        ≤ prodVert (M.cutProb r) (0 : M.V) y 1 2 :=
    fun y _ => exclVert_le_prodVert (M.cutProb r) (E1Sign.cutProb_lt_one M r)
      (Percolation.edgeExhaustion (E := Sym2 M.V)) Percolation.edgeExhaustion_mono
      Percolation.edgeExhaustion_cover (0 : M.V) y 1 2
  have hprodtop : ∀ y ∈ E1Sign.ballF M r,
      prodVert (M.cutProb r) (0 : M.V) y 1 2 ≠ ⊤ := by
    intro y _
    rw [prodVert, M.powMomentAt_cutProb_eq_cutMoment, M.powMomentAt_cutProb_eq_cutMoment]
    exact ENNReal.mul_ne_top h1 h2
  have hexcltop : ∀ y ∈ E1Sign.ballF M r,
      exclVert (M.cutProb r) (0 : M.V) y 1 2 ≠ ⊤ :=
    fun y hy => ne_top_of_le_ne_top (hprodtop y hy) (hexcl y hy)
  have hsumU : (∑ y ∈ E1Sign.ballF M r, exclVert (M.cutProb r) (0 : M.V) y 1 2)
      = M.exclMassQuad r := (exclMassQuad_eq_sum_exclVert M r).symm
  calc (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r
        - M.exclMassQuad r).toReal
      = (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 1 r * M.cutMoment 2 r).toReal
          - (M.exclMassQuad r).toReal := ENNReal.toReal_sub_of_le hle htop
    _ = (∑ y ∈ E1Sign.ballF M r, prodVert (M.cutProb r) (0 : M.V) y 1 2).toReal
          - (∑ y ∈ E1Sign.ballF M r, exclVert (M.cutProb r) (0 : M.V) y 1 2).toReal := by
        rw [sum_prodVert_cutProb M, hsumU]
    _ = (∑ y ∈ E1Sign.ballF M r, (prodVert (M.cutProb r) (0 : M.V) y 1 2).toReal)
          - ∑ y ∈ E1Sign.ballF M r, (exclVert (M.cutProb r) (0 : M.V) y 1 2).toReal := by
        rw [ENNReal.toReal_sum hprodtop, ENNReal.toReal_sum hexcltop]
    _ = ∑ y ∈ E1Sign.ballF M r,
          ((prodVert (M.cutProb r) (0 : M.V) y 1 2).toReal
            - (exclVert (M.cutProb r) (0 : M.V) y 1 2).toReal) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ y ∈ E1Sign.ballF M r, (gapVert (M.cutProb r) (0 : M.V) y 1 2).toReal := by
        refine Finset.sum_congr rfl fun y hy => ?_
        exact (ENNReal.toReal_sub_of_le (hexcl y hy) (hprodtop y hy)).symm

/-- **The per-vertex product gaps are dominated by the star window mass**, in `ℝ`.
This is the trivial half of (I.4.16) at the window level; the difference is the window
covariance.  It uses only `gapVert_le_starVert` termwise. -/
theorem sum_gapVert_toReal_le_connCubeMass_toReal (r : ℝ)
    (hc : ∀ y ∈ E1Sign.ballF M r, M.connCubeVertexMass r y ≠ ⊤) :
    ∑ y ∈ E1Sign.ballF M r, (gapVert (M.cutProb r) (0 : M.V) y 1 2).toReal
      ≤ (M.connCubeMass r).toReal := by
  classical
  let := Encodable.ofCountable (Sym2 M.V)
  have hsum : M.connCubeMass r = ∑ y ∈ E1Sign.ballF M r, starVert (M.cutProb r) (0 : M.V) y 3 :=
    connCubeMass_eq_sum_starVert M r
  have hstartop : ∀ y ∈ E1Sign.ballF M r,
      starVert (M.cutProb r) (0 : M.V) y 3 ≠ ⊤ := by
    intro y hy
    rw [starVert_cutProb_eq_connCubeVertexMass M r y]
    exact hc y hy
  rw [hsum, ENNReal.toReal_sum hstartop]
  refine Finset.sum_le_sum fun y _ => ?_
  exact ENNReal.toReal_mono (hstartop y ‹y ∈ E1Sign.ballF M r›)
    (gapVert_le_starVert (M.cutProb r) (E1Sign.cutProb_lt_one M r)
      (Percolation.edgeExhaustion (E := Sym2 M.V)) Percolation.edgeExhaustion_mono
      Percolation.edgeExhaustion_cover (0 : M.V) y 1 2)

end SourceModelData

end QZeroRepairAudit
end PercLib.CriticalLRP
