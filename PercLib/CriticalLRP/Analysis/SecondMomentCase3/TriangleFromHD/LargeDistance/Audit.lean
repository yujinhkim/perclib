/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m1.
Latest independent rebuild at production HEAD `bd25afb1130f7fe93446b447f9a68a4d3aba08cc`; reviewed scratch source `.scratch/review-smwznoz6j/m1/Audit.lean`.

Swarm `smwznoz6j`, member `m1`, direction `d2` — (G) non-vacuity of the literal Case 3 of (HD).

Axiom audit of the packet.  Every export must rest on exactly
`[propext, Classical.choice, Quot.sound]`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.LargeDistance.Main

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

open PercLib.CriticalLRP Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flat6C_pos
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.le_flatNorm6
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatNorm6_le_one_iff
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatNorm6_unitBall
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatNorm6_zero
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatNorm6_pos
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatNorm6_neg
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatNorm6_add_le
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatNorm6_smul
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatNorm6_continuous
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatSourceNorm6
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.toVec_flat6E1
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatNorm6_e1
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatSourceNorm6_dist_e1
#print axioms PercLib.CriticalLRP.Orchestration.FlatSix.flatSourceNorm6_dist_e1_lt_one
#print axioms PercLib.CriticalLRP.Orchestration.flatModel6
#print axioms PercLib.CriticalLRP.Orchestration.flatModel6_d
#print axioms PercLib.CriticalLRP.Orchestration.flatModel6_α
#print axioms PercLib.CriticalLRP.Orchestration.flatModel6_S

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_srcNorm_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPoint_eq_zero_of_dist_eq_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_case3HD_flatModel6
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3HDPos_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3HDLarge_of_case3HDPos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3HDLarge_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3HD_iff_case3HDPos_of_far
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tau_le_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_abs_tau_le_Wt_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3HDLarge_of_Wt_majorant
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3HDLarge_iff_Wt_majorant
