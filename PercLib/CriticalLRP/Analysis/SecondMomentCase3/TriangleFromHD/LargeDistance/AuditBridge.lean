/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m1.
Latest independent rebuild at production HEAD `bd25afb1130f7fe93446b447f9a68a4d3aba08cc`; reviewed scratch source `.scratch/review-smwznoz6j/m1/AuditBridge.lean`.

Axiom audit of the `Case3HDLarge` re-run of the Case-3 convolution chain.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.LargeDistance.Bridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

open PercLib.CriticalLRP Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tauConv_bound_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tauConvConv_bound_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openTriangleSelf_lt_top_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logRadialBound_openTriangle_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_nablaTail_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_case3HDLarge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_case3HDLarge
