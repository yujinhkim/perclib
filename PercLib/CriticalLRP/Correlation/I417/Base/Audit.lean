/- Independent axiom audit for the marked-tree and q = 1 polygon assembly. -/

module
public import PercLib.CriticalLRP.Correlation.I417.Base.Depth
public import PercLib.CriticalLRP.Correlation.I417.Base.QOne

/-!
Axiom audit for the marked-tree evaluation and q = 1 polygon composition. The
remaining `hjoint` marked tree-graph input is a percolation hypothesis, not an axiom.
-/

set_option linter.hashCommand false
set_option linter.style.longLine false
#print axioms PercLib.CriticalLRP.I417Base.tsum_wtE
#print axioms PercLib.CriticalLRP.I417Base.tsum_wtE_marked
#print axioms PercLib.CriticalLRP.I417Base.pathW_eq_iterPow
#print axioms PercLib.CriticalLRP.I417Base.iterPow_succ_right
#print axioms PercLib.CriticalLRP.I417Base.iterPow_comm
#print axioms PercLib.CriticalLRP.I417Base.tsum_iterPow_mul
#print axioms PercLib.CriticalLRP.I417Base.marked_diagram_by_depth
#print axioms PercLib.CriticalLRP.I417Base.q_one_polygon
