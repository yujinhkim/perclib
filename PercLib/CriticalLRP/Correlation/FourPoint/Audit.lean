/- Integrated from independently rebuilt Ultramath work.
Production base 3b6ff818cd3ac1a9cee99dcfff154a2ff4f85095.
Scratch source: ../../.ultramath/smwvp122a/m3/Audit.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.FourPoint.ProofBKHelpers

/-!
Axiom audit for the four-point cover and the BK-side ingredients: each main result must depend
only on `propext`, `Classical.choice` and `Quot.sound`.
-/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.FourPoint.tree_cover
#print axioms PercLib.CriticalLRP.FourPoint.cover_of_tree_le
#print axioms PercLib.CriticalLRP.FourPoint.cover_of_reachable
#print axioms PercLib.CriticalLRP.FourPoint.disjoint_of_dist_add
#print axioms PercLib.CriticalLRP.FourPoint.exists_three_arm_data
#print axioms PercLib.CriticalLRP.FourPoint.prob_union_le
#print axioms PercLib.CriticalLRP.FourPoint.mem_disjOcc3_of_walks
#print axioms PercLib.CriticalLRP.FourPoint.pair_eq_of_triple
