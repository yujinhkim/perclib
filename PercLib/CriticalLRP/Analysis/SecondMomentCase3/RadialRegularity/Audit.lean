/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f` with m3/m7 sources.
Integration based on production commit `caf06cb0a9face27c4dce7b4a13703d40d4568ac`.

# Axiom audit for the radial and first-moment Case-3 reductions
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.FirstMomentSource
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.Case3Composite

/-! # Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.exists_monotone_finset_exhausting
#print axioms PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.exists_windowFinsets
#print axioms PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.ac_and_ae_toReal_two_farTail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.secondMoment_asymptotic_case3_of_source_p21_no_ac
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.regularlyVarying_two_of_source_p21_no_ac
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_cutMoment_one_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_cutMassAt_ne_top_of_cutMoment_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutMassReal_atTop_of_uncutMean_eq_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_cutE1_of_triangle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutError_of_triangle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3_firstMoment_inputs_of_triangle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3_firstMoment_inputs_of_source
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_p21_hP_discharged
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_p21_hP_discharged
#print axioms
  PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_hP_discharged
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_p21_of_model
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_p21_of_model
