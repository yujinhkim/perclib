/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m3/Audit.lean.
-/
/-
Audit file: axiom footprint of the Case 1 decorrelation results.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Reduction
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Bridge
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Sharpness

/-!
# Axiom audit for the Case 1 (`d > 3α`) decorrelation estimate of Proposition I.4.20

Every result depends only on the three standard axioms
`propext`, `Classical.choice`, `Quot.sound`; there is no `sorry`, no custom axiom, and
no `native_decide`.
-/

#print axioms PercLib.CriticalLRP.I420Case1.cardFun_cluster_eq_clusterVol
#print axioms PercLib.CriticalLRP.I420Case1.mixedExcl_eq_sum_lintegral
#print axioms PercLib.CriticalLRP.I420Case1.mixedExcl_le_prodFactor
#print axioms PercLib.CriticalLRP.I420Case1.prodFactor_le_mixedExcl_add_window
#print axioms PercLib.CriticalLRP.I420Case1.windowMoment_le_powMoment
#print axioms PercLib.CriticalLRP.I420Case1.discrepancy_toReal
#print axioms PercLib.CriticalLRP.I420Case1.ratio_tendsto_one_of_window_bound
#print axioms PercLib.CriticalLRP.I420Case1.exponent_lt_of_three_alpha_lt
#print axioms PercLib.CriticalLRP.I420Case1.case1_decorrelation
#print axioms PercLib.CriticalLRP.I420Case1.wMom_order_of_treegraph
#print axioms PercLib.CriticalLRP.I420Case1.prodFactor_order_of_asymptotics
#print axioms PercLib.CriticalLRP.I420Case1.mixedExcl_one_one
#print axioms PercLib.CriticalLRP.I420Case1.mixedExcl_zero
#print axioms PercLib.CriticalLRP.I420Case1.windowMoment_zero
#print axioms PercLib.CriticalLRP.I420Case1.prodFactor_zero_eq
