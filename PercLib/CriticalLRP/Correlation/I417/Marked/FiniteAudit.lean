/- Independently rebuilt and verified at production revision
    eb9b71a3cf20a0fe9906271415f5b17efd80f5ad.
    Original scratch source is recorded below. -/
module

public import PercLib.CriticalLRP.Correlation.I417.Marked.Finite

/-!
Axiom and statement audit of the finite marked diagram integration.
-/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.FiniteMarkedJoin.posSumWtE_ne_top_of_finite
#print axioms PercLib.CriticalLRP.FiniteMarkedJoin.posSumWtE_toReal
#print axioms PercLib.CriticalLRP.FiniteMarkedJoin.labelledMarkedDiagram_toReal
#print axioms PercLib.CriticalLRP.FiniteMarkedJoin.sum_pinned_label
#print axioms PercLib.CriticalLRP.FiniteMarkedJoin.finite_marked_moment_le_polygon_toReal
#print axioms PercLib.CriticalLRP.FiniteMarkedJoin.finite_marked_moment_le_polygon_of_real

#check @PercLib.CriticalLRP.FiniteMarkedJoin.finite_marked_moment_le_polygon_of_real
