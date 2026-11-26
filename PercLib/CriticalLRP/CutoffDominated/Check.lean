/-
Axiom audit for the migrated cut-off domination module and the audit extras
(direction (C), member m2).

`import CutoffDominatedClean` loads the olean of `CutoffDominatedClean.lean` in this
directory, i.e. the audit copy of `PercLib/CriticalLRP/CutoffDominated.lean` at production
HEAD 6569f978 whose only edits are the four build-hygiene changes documented in its header.
`import AuditExtras` loads the additional lemmas proved in this directory.

The three permitted axioms are `propext`, `Classical.choice`, `Quot.sound`; every line below
must print exactly that triple.  `sorryAx` would show up as an extra entry.

The `#`-commands are the point of this file, so `linter.hashCommand` is disabled here (it is
not disabled in either module under audit).
-/
module

public import PercLib.CriticalLRP.CutoffDominated
public import PercLib.CriticalLRP.CutoffDominated.AuditExtras

/-! # Axiom audit for cutoff domination and the boundary-condition lemmas -/

set_option linter.hashCommand false

open scoped ENNReal

/-! ## The migrated statements (30 declarations) -/

#print axioms PercLib.CriticalLRP.CutoffDominated.uncutKernel_shift
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoffCoefficient_mem
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoffCoefficient_nonneg
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoff_parameter_lt
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoffSymKernel_le_scaled
#print axioms PercLib.CriticalLRP.CutoffDominated.bernoulliEdgeProb_le_of_mul_le
#print axioms PercLib.CriticalLRP.CutoffDominated.bernoulliEdgeProb_cutoff_le_scaled
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoff_edgeComparison
#print axioms PercLib.CriticalLRP.CutoffDominated.longRangeMeasure_cutoff_dominated
#print axioms PercLib.CriticalLRP.CutoffDominated.infiniteClusterProb_cutoff_le
#print axioms PercLib.CriticalLRP.CutoffDominated.infiniteClusterProb_cutoff_eq_zero
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_cutoff_le
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_cutoff_ne_top
#print axioms PercLib.CriticalLRP.CutoffDominated.uncutKernel_rootIndependent
#print axioms PercLib.CriticalLRP.CutoffDominated.uncutKernel_rootComparison
#print axioms PercLib.CriticalLRP.CutoffDominated.uncutKernel_rootComparison_any
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_sq_le_of_pointwise
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_sq_ne_top_of_pointwise
#print axioms PercLib.CriticalLRP.CutoffDominated.joint_windowMoment_ne_top_of_pointwise
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoff_clusterVol_sq_ne_top
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoff_joint_windowMoment_ne_top
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoffSymKernel_eq_cutoffKernel
#print axioms PercLib.CriticalLRP.CutoffDominated.kernelJ_eq_radialKernel
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoffSymKernel_loop
#print axioms PercLib.CriticalLRP.CutoffDominated.kernelJ_loop
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_cutoff_ne_top_of_subcritical
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_coefficient
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_coefficient_lt_one
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_coefficient_nonneg
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_cutoffSymKernel_le_scaled
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_longRangeMeasure_cutoff_dominated

/-! ## The audit extras proved in this directory (11 declarations) -/

#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.cutoffSymKernel_eq_zero_of_le_one
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.cutoffSymKernel_le_half_of_le_one
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.exists_cutoffCoefficient_domination
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.kernelJ_loop_eq
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.cutoffSymKernel_loop_le_of_nonneg
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.cutoffSymKernel_le_scaled_of_nonneg
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.hK0nn_sharp
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.not_forall_nonneg_kernelJ_of_K0_neg
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.cutoffCoefficient_lt_one_needs_K1
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.cutoffCoefficient_of_normalized
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.cutoffCoefficient_lt_one_iff
#print axioms PercLib.CriticalLRP.CutoffDominatedAudit.cutoffCoefficient_eq_one_iff
