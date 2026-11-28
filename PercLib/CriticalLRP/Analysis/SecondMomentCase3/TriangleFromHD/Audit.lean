/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m4/Audit.lean`.

Swarm `smwzlje3f`, member `m4`, direction `d4` — (E) the HD(3) / triangle / tail inputs.

# Axiom audit

Every exported theorem of this packet, checked for nonstandard axioms.  The permitted set is
`propext`, `Classical.choice`, `Quot.sound`; `sorryAx` would appear here if any proof were
incomplete, and no custom axiom is declared anywhere in the packet.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Main

set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section


#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.toVec_injective
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.toVec_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sρ_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.kernel_shift
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPointFunction_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tau_eq_twoPoint
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPoint_symm
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tau_eq_twoPoint_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tau_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tau_le_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ofReal_tau
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tau_le_of_case3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.log_inv_mul_rpow_le_Wt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_abs_tau_le_Wt

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.srcTransferConst_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.stage1Const_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.stage2Const_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tauConv_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tauConvConv_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tauConv_bound
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tauConvConv_bound
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPointFunction_eq_ofReal_tau
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openTriangle_eq_ofReal_tauConvConv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openTriangleSelf_lt_top_of_case3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.Wt_zero_two_le_logMajorant
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logRadialBound_openTriangle_of_case3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isLogErrorFunction_nablaTail_of_case3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_case3HD
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_case3HD
