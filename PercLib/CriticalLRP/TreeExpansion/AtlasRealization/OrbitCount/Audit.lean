/-
Independent UltraMath work, swarm `smwwsmqji`, member `m1`.
Production base `50c2eed0682a7e1b078ae771dbef463ebe00701d`, Lean 4.35.0.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.OrbitCount.Endpoint

/-!
# Axiom audit for the child-swap orbit count

Every result below is expected to depend on exactly `[propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, `native_decide` or custom axiom is used anywhere in `OrbitCount/`.
-/

set_option linter.hashCommand false
set_option autoImplicit false

open PercLib.CriticalLRP.TreeExpansion

#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.swapRel_trans
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.swapSetoid
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.mem_swapFiber_iff
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.swapFiber_disjoint_or_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.mem_swapOrbits
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.swapOrbits_card
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.swapOrbits_pairwiseDisjoint
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.biUnion_swapOrbits
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.sum_swapOrbits_card
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.sum_LT_eq_sum_orbits
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_mul
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_eq_div
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_fin_le_dfactorial
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.transversal_card
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.transversal_card_le_dfactorial
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.transversal_spec
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.sum_LT_eq_two_pow_mul_sum_transversal
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.treeSum_eq_sum_transversal
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.diagEvent_iUnion_subset_transversal
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.cover_union_transversal
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_conn_le_sum_transversal
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_conn_le_treeSum_of_swapTransport
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.treeGraphBound_of_swapTransport
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.moment_bound_of_swapTransport
