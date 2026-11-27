/-
Accepted from Ultramath `smwzg77c3`, member `m5`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d10`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Axiom audit for the finite-truncation bridge

Every exported theorem of `Defs.lean` and `Main.lean` is listed here.  The footprint is `propext`,
`Classical.choice`, `Quot.sound` only: no `sorryAx`, no custom axioms, no `native_decide`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroTransfer.Main

/-! # Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Exhaustion.starMoment_eq_iSup_labSum
#print axioms PercLib.CriticalLRP.Exhaustion.labSum_le_starMoment
#print axioms PercLib.CriticalLRP.Exhaustion.starMoment_le_of_labSum_le
#print axioms PercLib.CriticalLRP.Exhaustion.starMoment_le_iff_forall_labSum
#print axioms PercLib.CriticalLRP.Exhaustion.exists_labSum_gt_of_lt
#print axioms PercLib.CriticalLRP.Exhaustion.truncMass_le_cardFun
#print axioms PercLib.CriticalLRP.Exhaustion.iSup_truncMass
#print axioms PercLib.CriticalLRP.Exhaustion.iSup_truncMass_pow
#print axioms PercLib.CriticalLRP.Exhaustion.starMoment_eq_iSup_truncStar
#print axioms PercLib.CriticalLRP.Exhaustion.truncStar_le_starMoment
#print axioms PercLib.CriticalLRP.Exhaustion.starMoment_le_of_truncStar_le
#print axioms PercLib.CriticalLRP.Exhaustion.exists_truncStar_gt_of_lt
#print axioms PercLib.CriticalLRP.Exhaustion.starMoment_le_iff_forall_truncStar
#print axioms PercLib.CriticalLRP.Exhaustion.lintegral_cardFun_eq_iSup_truncMass
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hgapRHS_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_eq_iSup_labSum
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_eq_iSup_truncStar
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_le_of_labSum_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_le_of_truncStar_le
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_labSum_gt_of_connCubeVertexMass_gt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_eq_iSup_truncMass
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_toReal_le_of_labSum_le
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_toReal_le_of_truncStar_le
