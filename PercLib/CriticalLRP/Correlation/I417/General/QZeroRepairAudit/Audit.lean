/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

Ultramath swarm `smwziumdb`, member `m2`, direction `d5`.

# Axiom audit

Every exported theorem of this packet, checked against the three permitted axioms
(`propext`, `Classical.choice`, `Quot.sound`).  There is no `sorry`, `admit`, `native_decide`,
`sorryAx`, custom axiom or `False.elim` shortcut anywhere in the packet; the audit below is the
machine check of that claim.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Far
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Power

/-! # Independently reviewed Case-3 repair-audit module: Audit -/


set_option linter.hashCommand false
set_option linter.style.longLine false


open scoped ENNReal NNReal

namespace PercLib.CriticalLRP
namespace QZeroRepairAudit

#print axioms lintegral_eq_add_of_pointwise
#print axioms starVert_eq_connIndicator
#print axioms exclVert_eq_connIndicator
#print axioms measurable_connIndicator
#print axioms measurable_notConnIndicator
#print axioms measurable_clusterVol_mul
#print axioms clusterVol_eq_of_connects
#print axioms jointVert_eq_excl_add_star
#print axioms prodVert_le_jointVert
#print axioms exclVert_le_prodVert
#print axioms gapVert_le_starVert
#print axioms starVert_toReal_eq_gapVert_add_covVert
#print axioms exclVert_self_eq_zero
#print axioms starVert_self_eq_powMomentAt
#print axioms jointVert_self_eq_powMomentAt
#print axioms gapVert_self_eq_prodVert
#print axioms covVert_self_eq

namespace SourceModelData

#print axioms starVert_cutProb_eq_connCubeVertexMass
#print axioms connCubeMass_eq_sum_starVert
#print axioms exclMassQuad_eq_sum_exclVert
#print axioms sum_prodVert_cutProb
#print axioms windowNumerator_toReal_eq_sum_gapVert_toReal
#print axioms sum_gapVert_toReal_le_connCubeMass_toReal
#print axioms polyK_three_diag_le
#print axioms polyK_four_diag_le
#print axioms div_le_of_le_div_add_one
#print axioms diag_correction_lower_bound
#print axioms additive_const_ge
#print axioms connCubeVertexMass_toReal_eq_gapVert_add_covVert
#print axioms additive_of_gap_of_cov
#print axioms gapVert_diag_cutProb
#print axioms power_additive_impossible
#print axioms far_threshold_necessary
#print axioms not_hasFarStar_const

end SourceModelData

end QZeroRepairAudit
end PercLib.CriticalLRP
