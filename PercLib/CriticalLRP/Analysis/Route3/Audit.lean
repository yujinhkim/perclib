/- Audit of the independently reviewed tail-truncation and cutoff comparison. -/
module

public import PercLib.CriticalLRP.Analysis.Route3.Percolation

/-!
Axiom audit for the tail-truncation estimate and its source cutoff corollary.
-/

set_option autoImplicit false
set_option linter.hashCommand false

open PercLib.CriticalLRP.Analysis.Route3

#print axioms PercLib.CriticalLRP.Analysis.Route3.sum_range_inv_sqrt_le
#print axioms PercLib.CriticalLRP.Analysis.Route3.sum_Ico_inv_sq_le
#print axioms PercLib.CriticalLRP.Analysis.Route3.partialSum_le
#print axioms PercLib.CriticalLRP.Analysis.Route3.opt_arith
#print axioms PercLib.CriticalLRP.Analysis.Route3.cube_lintegral_le_of_tail
#print axioms PercLib.CriticalLRP.clusterVol_eq_top_or_nat
#print axioms PercLib.CriticalLRP.one_le_clusterVol
#print axioms PercLib.CriticalLRP.Orchestration.cutMoment_one_cube_le_two
#print axioms PercLib.CriticalLRP.Orchestration.cutLaw_le_criticalLaw
#print axioms PercLib.CriticalLRP.Orchestration.cutMoment_one_cube_le_two_of_tail
