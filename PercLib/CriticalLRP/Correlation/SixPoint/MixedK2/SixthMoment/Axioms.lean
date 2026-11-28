/-
Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m1.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m1/Axioms.lean`.
-/

/-
Ultramath `smwzqts7r`, member `m1`, direction `d2`.

# Axiom audit

Every exported theorem of this run, with its axiom set.  Only `propext`,
`Classical.choice` and `Quot.sound` are permitted; there is no `sorry`, `admit`,
`native_decide`, custom axiom or `DRAFT_SORRY` import.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Model
public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Obstruction

/-! Axiom audit for the conditional sixth-moment package and its route obstruction. -/

set_option linter.hashCommand false

@[expose] public section

#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.hubStarSix_tsum
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.hubStarSix_tsum_fin
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_six_split
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_fin6
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_fin6_perm
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_hubStarSix
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_slotK2Six
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_slotK2Six_six
#print axioms PercLib.CriticalLRP.TreeExpansion.SixFold.indicator_mul_two
#print axioms PercLib.CriticalLRP.TreeExpansion.SixFold.indicator_mul_six
#print axioms PercLib.CriticalLRP.TreeExpansion.SixFold.tsum_six_mul_with
#print axioms PercLib.CriticalLRP.TreeExpansion.SixFold.tsum_pow_six
#print axioms PercLib.CriticalLRP.TreeExpansion.SixFold.lintegral_cardFun_six_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_six_fin945_swap
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_fin945_const
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.doubleFactorial_nine
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.one_le_susceptibility
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.sixth_moment_of_sixCover
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.sixth_moment_of_eventCover
#print axioms PercLib.CriticalLRP.SixthMoment.cutProb_translate
#print axioms PercLib.CriticalLRP.SixthMoment.sixthMomentMixed_of_sixCover

#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.law_fwdArc_gen
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.law_conn_le_gen
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.tau_le_gen
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.jointP_le_gen
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.hubStarSix_le_gen
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.exp_ite
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.slotK2Six_le256
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.num_lt_nn
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.num_lt
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.eps_cube_le_law_conn_three256
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample.sixCover_false256
#print axioms PercLib.CriticalLRP.SixthMoment.p2ExclError_tendsto_zero_of_sixCover
#print axioms PercLib.CriticalLRP.SixthMoment.sixthMomentMixed_of_eventCover
