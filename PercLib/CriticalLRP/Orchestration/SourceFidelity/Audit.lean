/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m8.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m8/Audit.lean`.
-/

/-
Ultramath swarm `smwzqts7r`, member `m8`, direction `d3`.

Axiom audit of the integrated Case-1 / Case-2 / Case-3 / HDClosure / Corner /
CriticalVolumeTail packages at production HEAD
`e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`.

Each `#print axioms` line below is on a *headline* exported theorem of one of the eight
packages named in the task.  The expected output is `[propext, Classical.choice, Quot.sound]`;
anything else (in particular `sorryAx`) is a defect.
-/
module

public import PercLib.CriticalLRP.Orchestration.SourceFidelity.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase1
public import PercLib.CriticalLRP.Analysis.SecondMomentCase1.Source.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase2.Source.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.LargeDistance.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.UniformCutoff.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.CornerContinuity.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.HDClosure.Main
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Diagonal.Main

/-! Axiom checks for the representative source-fidelity review statements. -/

set_option linter.hashCommand false
set_option linter.style.longLine false

open PercLib.CriticalLRP Orchestration

@[expose] public section

/-! ## Case 1 (Proposition I.4.15, `d > 3α`) -/
#print axioms PercLib.CriticalLRP.CaseOne.cutMoment_four_mixed_le
#print axioms PercLib.CriticalLRP.CaseOne.p2ExclError_le_caseOne
#print axioms PercLib.CriticalLRP.CaseOne.eventually_p2ExclError_le_rpow
#print axioms PercLib.CriticalLRP.CaseOne.p2ExclError_tendsto_zero_of_caseOne
#print axioms PercLib.CriticalLRP.CaseOne.integrableOn_abs_div_p2ExclError
#print axioms PercLib.CriticalLRP.CaseOne.regularlyVarying_two_of_caseOne_no_ac
#print axioms PercLib.CriticalLRP.CaseOne.tendsto_div_two_of_caseOne_no_ac
#print axioms PercLib.CriticalLRP.CaseOne.exists_cube_comparable_of_caseOne_no_ac
#print axioms PercLib.CriticalLRP.CaseOne.momentGap_of_caseOne_no_ac
#print axioms PercLib.CriticalLRP.CaseOne.propositionI415_caseOne_no_ac

/-! ## Case 2 (Proposition I.4.15, `d = 3α` + (Hydro)) -/
#print axioms PercLib.CriticalLRP.CaseTwo.p2ExclError_le_caseTwo
#print axioms PercLib.CriticalLRP.CaseTwo.eventually_p2ExclError_le_rpow
#print axioms PercLib.CriticalLRP.CaseTwo.p2ExclError_tendsto_zero_of_caseTwo
#print axioms PercLib.CriticalLRP.CaseTwo.tightInterSecond_momentConst
#print axioms PercLib.CriticalLRP.CaseTwo.p2ExclError_tendsto_zero_of_caseTwo'

/-! ## Case 3 from the literal `Case3HD` -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openTriangleSelf_lt_top_of_case3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logRadialBound_openTriangle_of_case3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_nablaTail_of_case3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_case3HD

/-! ## `Case3HDLarge`: the honest, non-refutable form of (HD)(3) -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_case3HD_flatModel6
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPoint_eq_zero_of_dist_eq_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_srcNorm_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3HDLarge_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_abs_tau_le_Wt_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3HDLarge_iff_Wt_majorant

/-! ## The cited uncut critical volume tail and its uniform-cutoff form -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalVolumeTail_of_pointwise
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_criticalVolumeTail_of_tail_asymptotic
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_le_envelope
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_of_volumeTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_le_iSup_cutLaw
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_eq_iSup_cutLaw
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalVolumeTail_iff_uniform_cutTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_of_uniform_cutTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_eq_iSup_cutLaw_of_finiteWitness

/-! ## `I420Case3.HDClosure` -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hTri_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.case3TriangleTailData_of_case3HD
#print axioms PercLib.CriticalLRP.I420Case3.firstMomentAsymptotic_of_critical_divergence_ae
#print axioms PercLib.CriticalLRP.I420Case3.exists_case3_i421_cutPoly_source_of_case3HD
#print axioms PercLib.CriticalLRP.I420Case3.forall_case3_i421_cutPoly_source_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_case3HD_of_srcNorm_le_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_lt_srcNorm_of_case3HD

/-! ## `CornerContinuity` -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_not_continuousAt_cutEdgeDeriv_at_dist
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_exists_discontinuous_cutEdgeDeriv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_hcontinf_corrected
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_ae_continuousAt_sMomentInfFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_hcontinf_iff_uniform_windowTail

/-! ## `QZeroRepairAudit.Diagonal` -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_le_three_mul_chi_pow_five
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasUniformWeightStar_one_two_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasCovBound_diag
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasCovBound_of_starWeighted
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.covVert_diag_toReal_eq
