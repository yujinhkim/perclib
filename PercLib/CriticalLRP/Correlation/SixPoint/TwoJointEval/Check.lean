/-
Axiom audit for the `j = 2` two-joint middle-split evaluation.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointEval.Assembly

/-!
# Axiom audit for the middle-split evaluation

Only the middle split is evaluated; other splits and the moment assembly remain open.
-/


set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.midSlotK2_swap
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.combSystem_union_le
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_union_le
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_seven_perm
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.midSlot_peel_joint
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.midSlotK2_tsum_root_joint
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.midSlot_peel_chain
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.midSlotK2_tsum_root_chain
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.midSlotK2_tsum_root_joint_of_perm
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.midSlotK2_tsum_root_chain_of_perm
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.residual_chain_tsum
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin15_fin7_le
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat0
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat1
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat2
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat3
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat4
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat5
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat7
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat8
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat9
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat10
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat11
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat12
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat13
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_pat14
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.sixShape_mid_tsum_le_id
#print axioms PercLib.CriticalLRP.SixPoint.TwoJointEval.pat_six
