/-
An independently rebuilt direction (Ultramath swarm `smwwt6noq`, member `m2`, direction B).
Production base `4c53bb5a8e76a4358a426adf71169b916b90f51f`.

Axiom audit of the final results: every `#print axioms` below must list only `propext`,
`Classical.choice` and `Quot.sound`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Marked.FiniteSum

/-!
# Axiom audit
-/

@[expose] public section

namespace PercLib.CriticalLRP.I417Marked

/-! ## The label-to-position API -/

#print axioms markPos_spec
#print axioms markPos_unique
#print axioms existsUnique_markPos
#print axioms card_filter_markPos
#print axioms depth_pos
#print axioms markDepth_le

/-! ## The labelled marked shape family and its depth coefficients -/

#print axioms card_markedShapes
#print axioms sum_markedShapes
#print axioms markedShapes_numLeaves
#print axioms markedShapes_depth_le
#print axioms markedCount_eq_zero_of_lt
#print axioms markedCount_eq_zero_of_gt
#print axioms markedCount_le_card
#print axioms sum_markedCount

/-! ## The exact marked diagram reduction -/

#print axioms markedDiagram_eq_polygon
#print axioms labelledMarkedDiagram_eq_markedDiagram
#print axioms labelledMarkedDiagram_eq_polygon

/-! ## The finite-vertex form -/

#print axioms tsum_label_eq_sum
#print axioms posSumWtE_eq_sum
#print axioms labelledMarkedDiagram_eq_finiteSum

/-! ## The `p = 0` and `p = 1` evaluations -/

#print axioms labelledMarkedDiagram_zero
#print axioms markedDiagram_zero
#print axioms markedCount_one
#print axioms markedCount_zero
#print axioms markedPolygonBound_zero
#print axioms markedPolygonBound_one
#print axioms labelledMarkedDiagram_one

end PercLib.CriticalLRP.I417Marked
