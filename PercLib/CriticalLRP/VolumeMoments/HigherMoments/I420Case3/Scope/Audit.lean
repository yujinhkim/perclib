/- Integrated from independently verified `.ultramath/smwxyesaw/m2/Axioms.lean`
at production base `6eb8b0b660d7d9049a9fc25c7424bf10dbd723f6`. -/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Measurability
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.Divergence
public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case23
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE
public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.CornerSafe
public import PercLib.CriticalLRP.Analysis.TriTailSqrt
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffDefect.Limit
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffDefect.LogIntegrable

/-! # Axiom audit of the Case-3 scope dependencies -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.I420Case3.cutError
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3
#print axioms PercLib.CriticalLRP.I420Case3.openTriangleSelf_lt_top_of_source_sqrt
#print axioms PercLib.CriticalLRP.I420Case3.tendsto_cutError_of_tendsto_cutE1
#print axioms PercLib.CriticalLRP.I420Case3.case3_i421_cutPoly_source_of_HD_case3
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3_flux
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite
#print axioms PercLib.CriticalLRP.I420Case3.exists_case3_i421_cutPoly_source
#print axioms PercLib.CriticalLRP.I42C.first_moment_asymptotic_of_rpow_lower
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_nablaTail_of_HD_case2_or_case3
#print axioms PercLib.CriticalLRP.I420Case3.powMomentAt_cutProb_apply_eq_zero
#print axioms PercLib.CriticalLRP.PivotFlux.cutMass_ODE_of_flux
#print axioms PercLib.CriticalLRP.PivotFlux.tendsto_cutE0
#print axioms PercLib.CriticalLRP.CornerSafe.tendsto_one_sub_mul
#print axioms PercLib.CriticalLRP.TriTail.openTriangleSelf_lt_top_of_sqrtKernel
#print axioms PercLib.CriticalLRP.Orchestration.isLogErrorFunction_nablaTail_of_HD_third_disjunct
#print axioms PercLib.CriticalLRP.Orchestration.isLogErrorFunction_nablaTail_of_HD3
#print axioms PercLib.CriticalLRP.CutoffDefect.cutE1_tendsto_zero_of_triangleCondition
#print axioms PercLib.CriticalLRP.CutoffDefect.measurable_cutE1_of_measurable_stats
#print axioms PercLib.CriticalLRP.CutoffDefect.measurable_ball_ncard
#print axioms PercLib.CriticalLRP.I420Case3.measurable_cutE0
#print axioms PercLib.CriticalLRP.I420Case3.measurable_cutError_of_measurables
#print axioms PercLib.CriticalLRP.I420Case3.measurable_cutError_of_stats
