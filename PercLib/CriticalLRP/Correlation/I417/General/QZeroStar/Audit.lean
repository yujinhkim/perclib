/-
Axiom audit for `Correlation/I417/General/QZeroStar`.  Only the three standard Lean axioms may appear.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main

/-! # Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.I417Gen.rawDiff_add_starMoment
#print axioms PercLib.CriticalLRP.I417Gen.momentProd_sub_rawDiff_right_zero
#print axioms PercLib.CriticalLRP.I417Gen.momentGap_toReal_right_zero
#print axioms PercLib.CriticalLRP.I417Gen.momentPow_eq_starMoment_add_rawDiff
#print axioms PercLib.CriticalLRP.I417Gen.starMoment_le_momentPow
#print axioms PercLib.CriticalLRP.I417Gen.starMoment_eq_tsum_labelEvent
#print axioms PercLib.CriticalLRP.I417Gen.starMoment_pos
#print axioms PercLib.CriticalLRP.I417Gen.markedFamily_q_zero_eq_zero
#print axioms PercLib.CriticalLRP.I417Gen.markedFamily_q_zero_lt_starMoment
#print axioms PercLib.CriticalLRP.I417Gen.momentProd_sub_rawDiff_zero_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_eq_starMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_eq_momentGap
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_eq_momentGap_of_cutMoment
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_le_cutMoment_three
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_eq_sum_starMoment
