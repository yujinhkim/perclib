/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`: axiom audit of every declaration of this direction.

All of them must rest only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no `native_decide`, no custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.AEHigherMoments.CubicModel


/-! # Almost-everywhere higher-moment interface: Audit -/

set_option linter.hashCommand false

@[expose] public section

#print axioms PercLib.CriticalLRP.Analysis.AE.ae_uIoc_of_ae_restrict_Icc
#print axioms PercLib.CriticalLRP.Analysis.AE.intervalIntegral_ae_deriv_eq_sub
#print axioms PercLib.CriticalLRP.Analysis.AE.sub_le_integral_of_ae_hasDerivAt_of_le
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_restrict_Icc_of_ae_restrict_Ici
#print axioms PercLib.CriticalLRP.Analysis.AE.absolutelyContinuousOnInterval_inv_rpow
#print axioms PercLib.CriticalLRP.Analysis.AE.AbsolutelyContinuousOnInterval.div_rpow
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_hasDerivAt_div_rpow
#print axioms PercLib.CriticalLRP.Analysis.AE.div_rpow_deriv_le_of_driving
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_normalized_increment_le_of_driving_bound
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_eventually_ratio_le_of_driving_bound
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_lemma_I_4_22_of_defect_bound
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_lemma_I_4_22_of_ae_sharp_bound
#print axioms PercLib.CriticalLRP.Analysis.AE.ae_le_of_forall_ae_one_add_mul
#print axioms PercLib.CriticalLRP.Analysis.AE.exists_defect_of_eventually_one_add
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_ae
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_ae_eps
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_of_percolation_ae
#print axioms
  PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_of_percolation_ratio_ae
#print axioms PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_three_ratio_ae
#print axioms
  PercLib.CriticalLRP.VolumeMoments.HigherMoments.moment_upper_bound_three_ratio_of_pos_ae
#print axioms PercLib.CriticalLRP.I420Case3.case3_moment_three_bound_of_HD_case3_ae
