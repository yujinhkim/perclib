/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m2`, direction `d1`.

# Axiom audit for the summed ℓ = 3 Case-3 packet

Every export below must rest only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).  `#print axioms` is a command, so the
Mathlib hash-command linter is switched off for it here; nothing else is excluded.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.SummedThree.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.SummedThree.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.SummedThree.Obstruction

set_option linter.hashCommand false
set_option linter.style.longLine false

/-! ## Definitions -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3ThreeDriver
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3TailDriver
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3SplitDriver
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3ThreeDriver_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3TailDriver_nonneg

/-! ## The ℓ = 3 slot: summed near/far bound and its normalized form -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_polyK_three_ballF_le_near_far
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_polyK_three_ballF_le_card_mul_case3ThreeDriver
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_nearSets_dist

/-! ## The corrected Case-3 consumer -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_perVertex_le_split
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_of_splitGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_of_nearSets
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_le_of_source_threeDriver

/-! ## The `E_{2,r}` estimates -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ratio_le_of_moment_gap_split
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_of_splitGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_of_nearSets
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_of_source_split

/-! ## The driver is a genuine Case-3 driver: nonnegative, vanishing, log-integrable -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3ThreeDriver_nonneg_of_one_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_card_div_ball_le_rpow
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_comp_rpow
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_case3ThreeDriver
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.logarithmicallyIntegrable_case3ThreeDriver

/-! ## The Case-3 endpoint -/

#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_source_split

/-! ## The obstruction: the vertexwise ℓ = 3 hypothesis `hT3` is false -/

#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.not_forall_polyK_three_le_case3Driver
