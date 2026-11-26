/-
Axiom audit and exact statement record for direction `(B) UNRESTRICTED-FIBRE EVALUATION`
(swarm `smwxtabcx`, member `m2`).

Every theorem of this package must rest only on the three standard axioms `propext`,
`Classical.choice`, `Quot.sound`.  `#print` of the main theorems follows the audit so that the
exact statements (all premises included) are recorded in the build log.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.SummedFresh.Main
public import PercLib.CriticalLRP.Correlation.I417.SummedFresh.Compose

/-! Axiom audit and exact statement record for the summed fresh profile and pair composition. -/

set_option linter.hashCommand false

open PercLib.CriticalLRP.I417SummedFresh

/-! ## Reindexing -/

#print axioms prod_tau_eq_histW
#print axioms tsum_pinned_swap

/-! ## Evaluation of the history sum -/

#print axioms tau_symm
#print axioms tsum_histW_tsum_eq_freshProfileSum

/-! ## The summed fresh bound -/

#print axioms tsum_freshMark_le_freshProfileSum
#print axioms tsum_freshMark_le_freshProfileSum_one
#print axioms summedFreshProfile
#print axioms tsum_freshMark_le_freshPoly
#print axioms freshProfileSum_eq_freshPoly

/-! ## The outer moment composition -/

#print axioms tsum_finsetSum
#print axioms tsum_fin_snd
#print axioms tsum_pair_monomial
#print axioms tsum_base_mul_fresh
#print axioms mul_compCoeff
#print axioms moment_gap_le_pairPoly

/-! ## Exact statements -/

#print moment_gap_le_pairPoly
#print tsum_freshMark_le_freshProfileSum
#print summedFreshProfile
#print tsum_pinned_swap
#print tsum_histW_tsum_eq_freshProfileSum
#print tsum_freshMark_le_freshPoly
#print SummedFreshProfile
#print freshProfileSum
