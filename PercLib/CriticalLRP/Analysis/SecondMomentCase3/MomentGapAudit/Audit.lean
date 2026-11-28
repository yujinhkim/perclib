/-
Ultramath swarm `smwzlje3f`, member `m1`, direction `d7`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.scratch/review-smwzlje3f/m1/AxiomAudit.lean`.

# Axiom audit for the d7 Case-3 moment-gap audit

Each exported theorem of `Audit.lean` is checked here to depend only on `propext`,
`Classical.choice` and `Quot.sound` (no `sorryAx`, no custom axioms).
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.MomentGapAudit.Main

/-! Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Case3MomentGapAudit.rpow_cube_eq
#print axioms PercLib.CriticalLRP.Case3MomentGapAudit.eventually_sandwich_of_tendsto_div
#print axioms PercLib.CriticalLRP.Case3MomentGapAudit.exists_const_mul_cube_le_iff
#print axioms PercLib.CriticalLRP.Case3MomentGapAudit.jensen_does_not_give_momentGap
#print axioms PercLib.CriticalLRP.Case3MomentGapAudit.tendsto_log_mul_div_log
#print axioms PercLib.CriticalLRP.Case3MomentGapAudit.regularlyVarying_div_log
#print axioms PercLib.CriticalLRP.Case3MomentGapAudit.regularlyVarying_does_not_give_power_lower
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.betaCrit_coe_pos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_sandwich_cutMassAt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_iff_secondMomentLower
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.MomentGapAt.mono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_forces_cutMoment_two_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_forces_cutMoment_two_tendsto_atTop
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_of_tendsto_normalized
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGapAt_to_secondMomentLowerAt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMomentLowerAt_to_momentGapAt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.mul_cube_div_rpow_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.mul_cube_div_rpow_tendsto
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGapAt_mul_pow_three_le_of_tendsto_normalized
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGapAt_of_mul_pow_three_lt_tendsto_normalized
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_iff_pos_limit
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_iff_exists_eventually_le_div
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.betaCrit_coe_ne_zero_of_hP
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_two_ne_top_of_hP_of_momentGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_one_ne_top_of_hP_of_momentGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_p2ExclError_of_hP_of_momentGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_p2Ebar_of_hP_of_momentGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_rhsScalarTwo_of_hP_of_momentGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_cutE0_of_source
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_source_p21_core
