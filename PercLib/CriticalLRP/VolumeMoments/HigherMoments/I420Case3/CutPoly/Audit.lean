/-
Axiom audit for direction (B), Case 3 of Proposition I.4.20.

Only the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) may occur;
no `sorryAx`, no `Lean.ofReduceBool`/`Lean.trustCompiler` (`native_decide`), no custom axioms.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Bridge

/-! # Axiom audit for the cutoff polygon package -/

open PercLib.CriticalLRP.I420Case3

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I420Case3.cutPoly
#print axioms PercLib.CriticalLRP.I420Case3.cutPoly_zero
#print axioms PercLib.CriticalLRP.I420Case3.cutPoly_one
#print axioms PercLib.CriticalLRP.I420Case3.powMomentAt_cutProb_one
#print axioms PercLib.CriticalLRP.I420Case3.cutPoly_eq_Kpow
#print axioms PercLib.CriticalLRP.I420Case3.cutPoly_nonneg
#print axioms PercLib.CriticalLRP.I420Case3.one_le_polyK_three_of_chi_ne_top
#print axioms PercLib.CriticalLRP.I420Case3.CutPoly.cutPoly_le_rate
#print axioms PercLib.CriticalLRP.I420Case3.exists_hasPolygonBound_cutPoly
#print axioms PercLib.CriticalLRP.I420Case3.one_le_Bpoly_of_hasPolygonBound
#print axioms PercLib.CriticalLRP.I420Case3.not_tendsto_zero_of_one_le_eventually
#print axioms PercLib.CriticalLRP.I420Case3.no_vanishing_uniform_polygon_factor
#print axioms PercLib.CriticalLRP.I420Case3.not_exists_vanishing_hasPolygonBound
#print axioms PercLib.CriticalLRP.I420Case3.tendsto_rate_of_nablaTail
#print axioms PercLib.CriticalLRP.I420Case3.tendsto_polygonFactor
#print axioms PercLib.CriticalLRP.I420Case3.prodFactor_le_mixedExcl_add_cutPoly
#print axioms PercLib.CriticalLRP.AuditM2.iterPow_eq_Kpow
#print axioms PercLib.CriticalLRP.AuditM2.cutPoly_eq_iterPow_cutProb
#print axioms PercLib.CriticalLRP.AuditM2.iterPow_cutProb_zero_eq_cutPoly_zero
#print axioms PercLib.CriticalLRP.AuditM2.iterPow_cutProb_one_eq_cutPoly_one
#print axioms PercLib.CriticalLRP.AuditM2.cutProb_lt_one
#print axioms PercLib.CriticalLRP.AuditM2.meanVol_cutProb_eq_zero
#print axioms PercLib.CriticalLRP.AuditM2.hasTreeExpansion_cutPoly
#print axioms PercLib.CriticalLRP.AuditM2.cutMassAt_ne_top_of_hP
