module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroDiagonal.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.SummedThree.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.SummedThree.Obstruction
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.MarkedPolygon
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.EllThreeObstruction
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ConsumerGap
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.FirstMomentLogError
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3Bundle
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3Bundle.Audit
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.NoGo
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Repaired
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Case3Windowed

/-! # Axiom audit of the Case-3 second-moment assembly -/

set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

open PercLib.CriticalLRP PercLib.CriticalLRP.Orchestration PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms SourceModelData.connCubeMass_eq_sum_vertex
#print axioms SourceModelData.connCubeMass_le_of_windowGap
#print axioms SourceModelData.p2ExclError_le_case3Driver
#print axioms SourceModelData.p2ExclError_tendsto_zero_of_case3
#print axioms SourceModelData.logIntegrable_p2ExclError_of_case3
#print axioms SourceModelData.logIntegrable_p2Ebar
#print axioms SourceModelData.exists_momentGap_of_volumeTail
#print axioms SourceModelData.regularlyVarying_two_of_case3
#print axioms SourceModelData.tendsto_div_two_of_case3
#print axioms SourceModelData.secondMoment_asymptotic_case3
#print axioms SourceModelData.exists_polygonBound_four
#print axioms SourceModelData.case3Driver_isLogErrorFunction
#print axioms SecondMomentCase3.sum_perVertex_le
#print axioms SecondMomentCase3.ratio_le_of_moment_gap
#print axioms PercLib.CriticalLRP.I417Gen.rawDiff_add_starMoment
#print axioms PercLib.CriticalLRP.I417Gen.starMoment_eq_tsum_labelEvent
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_eq_starMoment
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_eq_momentGap_of_cutMoment
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_eq_sum_starMoment
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.not_forall_polyK_three_le_case3Driver
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_source_split
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_connCubeMass_toReal_le_markedPolygon
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3_hypothesis_bundle
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.SecondMomentCase3.hcase3_unsatisfiable
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.SecondMomentCase3.p2ExclError_le_case3_of_tri
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.SecondMomentCase3.logIntegrable_p2ExclError_of_case3_repaired
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_p2H
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3_firstMoment_inputs
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3_polygon_bundle
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.windowPolyKThree_le_case3Driver_eventually
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_windowedEllThreeGap
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_of_windowedGap
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_repaired_case3_polygon_bundle
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_source
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_case3_error_rate
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_case3_error_logIntegrable
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_div_two_of_case3_windowed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.diag_contradiction
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.not_hasPerVertexTwoTermHgap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_windowGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowSum_le_of_repaired
