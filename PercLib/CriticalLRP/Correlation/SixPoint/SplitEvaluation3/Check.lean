/-
Swarm `smwxk27m7`, member `m2`, direction (A) `SOCKET-ORDER-TO-SHAPE-BOUNDS`.

Axiom audit of every theorem of this directory.  The only admissible axioms are `propext`,
`Classical.choice` and `Quot.sound`; every line below must print a subset of those
(`#print axioms` lists `sorryAx` if any proof is incomplete, and any `axiom` of the file).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation3.Final

/-! Axiom audit for the canonical root-class bounds and the closed `p = 5`, `k = 2` case. -/

set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.style.setOption false

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.combSystem_one_union_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.shapeTotal_patSlot0_zero_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.shapeTotal_patSlot2_zero_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.shapeTotal_patSlot0_one_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.shapeTotal_patSlot2_one_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.shapeTotal_patSlot0_five_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.shapeTotal_patSlot2_five_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.shapeTotal_patSlot0_six_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.shapeTotal_patSlot2_six_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.shapeTotal_rootSlot_le_0156
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.fifth_moment_k2_le_of_rootSlot_three_four
/-! ### The assembled end-to-end theorems (with `m1`'s verified `j = 3` input) -/
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.fifth_moment_k2_le_of_rootSlot_four
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.fifth_moment_k2_le_of_rootSlot_three_four'
/-! ### The re-read `m1` `j = 3` inputs themselves -/
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeTotal_rootSlot0_three_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeTotal_rootSlot2_three_le
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.J3.shapeTotal_three_le
#print axioms SocketMirror.combSystem_three_iff_four
#print axioms SocketMirror.shapeTotal_three_eq_four
#print axioms SocketMirror.shapeTotal_patSlot0_four_le_of_three
#print axioms SocketMirror.shapeTotal_patSlot2_four_le_of_three
/-! ### The unconditional invariant-group `p = 5`, `k = 2` theorem -/

#print axioms PercLib.CriticalLRP.SixPoint.SplitEval3.fifth_moment_mixed_k2_le
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_fifth_moment_mixed_k2_le
