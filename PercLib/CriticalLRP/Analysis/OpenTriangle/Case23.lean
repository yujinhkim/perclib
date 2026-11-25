/-
Lemma I.4.3: logarithmic integrability of the normalized-source open-triangle tail
under either of the two high-dimensional two-point dominations.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case2Literal.Link
public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case3SrcNorm.Main

/-!
# Lemma I.4.3, Cases 2 and 3

The hypothesis is literally the disjunction of the second and third alternatives of
`Orchestration.HD`. The conclusion is `Analysis.IsLogErrorFunction` of the real-valued
`M.nablaTail`, built from the literal uncut open triangle at the actual normalized source norm.
Neither alternative is proved here; each remains a source hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration

/-- **Lemma I.4.3.** If Case 2 or Case 3 of `(HD)` holds, the normalized-source open-triangle
tail is a logarithmically integrable error function. The disjunction is exactly the union of
those two alternatives, not the whole `(HD)` disjunction (which also includes Case 1). -/
theorem isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (M : SourceModelData)
    (h :
      (6 < M.d ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
        M.twoPoint M.betaCrit x y ≤ C * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) ∨
      (M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
        M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
          (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  rcases h with hcase2 | hcase3
  · exact M.isLogErrorFunction_nablaTail_of_HD_second_disjunct hcase2
  · exact Orchestration.isLogErrorFunction_nablaTail_of_HD_third_disjunct M hcase3

end PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_nablaTail_of_HD_case2_or_case3
