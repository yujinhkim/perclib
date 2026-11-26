/-
Axiom audit for direction `FREE-ARM-PROFILE-ASSEMBLY` (swarm `smwxh86dl`, member `m2`).

Every theorem of this package must rest only on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound`.  The audit also re-audits the reused `smwxfstjy/m1` fibre
package (`FibreCheck.lean`) so that the chain is audited end to end.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Profile.Profile

/-!
# Assembly of the actual pinned-history cover into `genFreshProfile`

Uses the real split-choice/fibre decomposition; the bound is not a general marked-moment theorem.
-/


set_option linter.hashCommand false

open PercLib.CriticalLRP.I417FreshProfile

/-! ## Kernel and branch bounds -/

#print axioms iterPow_le_chi_pow
#print axioms tsum_histFibre_markDepth_symm
#print axioms histFibre_le_branchVal
#print axioms histFibre_le_profileTerm

/-! ## Coefficients and grouping -/

#print axioms mem_Icc_markDepthK
#print axioms card_depthFiber
#print axioms sum_markDepthK_mul

/-! ## Branch and history sums -/

#print axioms tsum_histFibre_le_genProfileSum
#print axioms tsum_histW_eq_tsum_histFibre
#print axioms tsum_pinned_le_tsum
#print axioms tsum_histW_le_genProfileSum
#print axioms tsum_pinned_histW_le_genProfileSum

/-! ## The event-level assembly -/

#print axioms genProfileSum_eq
#print axioms genShape_measure_le_genFreshProfile
#print axioms genFreshEval_genCoeff
#print axioms freshMark_measure_le_genFreshProfile
#print axioms freshMark_measure_le_freshPoly_genCoeff
#print axioms sum_depthCount_eq_card
