/-
Axiom audit for log-convex cluster moments and the Case 3 denominator comparison.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.MomentLogConvex.Main

/-! # Axiom audit
-/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I420Case3.MomentLogConvex.clusterVol_rpow_half_mul
#print axioms PercLib.CriticalLRP.I420Case3.MomentLogConvex.powMomentAt_succ_le_rpow
#print axioms PercLib.CriticalLRP.I420Case3.MomentLogConvex.powMomentAt_succ_sq_le
#print axioms PercLib.CriticalLRP.I420Case3.MomentLogConvex.momR_succ_sq_le
#print axioms PercLib.CriticalLRP.I420Case3.MomentLogConvex.momR_mul_one_ge
#print axioms PercLib.CriticalLRP.I420Case3.MomentLogConvex.momR_two_pow_mul_le
#print axioms PercLib.CriticalLRP.I420Case3.MomentLogConvex.biasTarget_le_mul_momR
#print axioms PercLib.CriticalLRP.I420Case3.biasTarget_le_mul_momOf
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_of_hIH'
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid'
