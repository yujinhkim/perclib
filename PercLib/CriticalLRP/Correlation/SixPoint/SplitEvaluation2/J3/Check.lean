/-
Swarm `smwxk27m7`, member `m1`, direction `d2` (`J3-EVENT-BRIDGE`).

Axiom audit of every submitted result.  Allowed: `propext`, `Classical.choice`, `Quot.sound`.
Any other name in the output (in particular `sorryAx` or a project axiom) is a failure.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.J3.J3Shape

/-! Axiom audit for the `j = 3` event bridge and canonical shape-mass bounds. -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.combSystem_twoJointThree_three
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.twoJointThree_le_slot3
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.combSystem_three_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.combSystem_union_le_three
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.sixShape_union_le_three
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.tsum_slot3_root0
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.tsum_slot3_root2
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeMass_rootSlot0_three_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeMass_rootSlot2_three_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeTotal_rootSlot0_three_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeTotal_rootSlot2_three_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeTotal_rootSlot_three_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeTotal_three_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.pattern_three
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.pattern_three_events
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.fifth_moment_k2_le_of_rootSlot_bounds_away
