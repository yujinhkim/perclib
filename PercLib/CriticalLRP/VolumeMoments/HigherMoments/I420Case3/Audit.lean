/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Axiom audit for the Case 3 modules.  Independent Ultramath work.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Compare

/-!
# Axiom audit for the Case 3 decorrelation estimate of Proposition I.4.20

Every result below is expected to depend only on the three standard axioms
`propext`, `Classical.choice` and `Quot.sound`: there is no `sorry`, no `admit`, no
`native_decide` and no custom axiom in the `I420Case3` modules.
-/

#print axioms PercLib.CriticalLRP.I420Case3.polygon_pow_identity
#print axioms PercLib.CriticalLRP.I420Case3.sum_treePoly_eq
#print axioms PercLib.CriticalLRP.I420Case3.sum_poly_le
#print axioms PercLib.CriticalLRP.I420Case3.polygon_sum_le
#print axioms PercLib.CriticalLRP.I420Case3.prodFactor_le_mixedExcl_add_polygon
#print axioms PercLib.CriticalLRP.I420Case3.one_le_clusterVol_pow
#print axioms PercLib.CriticalLRP.I420Case3.one_le_powMomentAt
#print axioms PercLib.CriticalLRP.I420Case3.one_le_momR
#print axioms PercLib.CriticalLRP.I420Case3.momR_pos
#print axioms PercLib.CriticalLRP.I420Case3.prodFactor_ne_top
#print axioms PercLib.CriticalLRP.I420Case3.discrepancy_toReal_le_polygon
#print axioms PercLib.CriticalLRP.I420Case3.discR_le_polygon
#print axioms PercLib.CriticalLRP.I420Case3.discR_nonneg
#print axioms PercLib.CriticalLRP.I420Case3.succ_add_sub_eq
#print axioms PercLib.CriticalLRP.I420Case3.exponent_eq
#print axioms PercLib.CriticalLRP.I420Case3.biasTarget_ge_of_m2_ge
#print axioms PercLib.CriticalLRP.I420Case3.biasTarget_pos
#print axioms PercLib.CriticalLRP.I420Case3.tendsto_div_biasTarget_zero
#print axioms PercLib.CriticalLRP.I420Case3.tendsto_div_zero_of_le_mul
#print axioms PercLib.CriticalLRP.I420Case3.tendsto_one_of_tendsto_div_sub
#print axioms PercLib.CriticalLRP.I420Case3.case3_i421_family
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAmid_of_i421
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid
#print axioms PercLib.CriticalLRP.I420Case3.mixedMoment_mul_eq
#print axioms PercLib.CriticalLRP.I420Case3.eventually_comparison_of_ih
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_of_hIH
