/-
Axiom audit for the `ℓ = 3` obstruction and the column-sum repair.  Every export must depend
only on the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.EllThreeObstruction

/-! # Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_tendsto_case3Driver_zero_of_uniform_ell_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3Driver_bundle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3_hypothesis_bundle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3_hypothesis_bundle_of_cutMoment_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_polyK_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_ballF_polyK_three_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_perVertex_le_colsum
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_le_of_windowGap_colsum
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_le_of_windowGap_chi_cube
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_colsum
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_chi_cube
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_chi_cube_div_ball_ncard_atTop
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_chi_cube_div_ball_ncard_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_p2ExclError_zero_of_case1
