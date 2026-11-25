/- Integrated from reviewed Ultramath combinatorics.
Production base e387aba5a75e414ca007951b6333ffa5af720573.
Scratch source: ../../.ultramath/smwvlmbqa/m1/Audit.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Atlas.Check
public import PercLib.CriticalLRP.TreeExpansion.Atlas.Structure

/-! # Axiom audit of the I.4.16 atlas layer

`lean -DautoImplicit=false Audit.lean` prints the axioms used by every headline theorem; each
must be a subset of `propext`, `Classical.choice`, `Quot.sound`.  The source contains no
`sorry`, `admit`, `native_decide`, `partial` or custom `axiom` (see `audit.sh`).
-/

@[expose] public section

set_option autoImplicit false

open PercLib.CriticalLRP.TreeExpansion

#print axioms RTree.card_lpaths
#print axioms RTree.card_ipaths
#print axioms RTree.card_evenHubs_add_card_oddHubs
#print axioms RTree.ceil_half_le_max_class
#print axioms RTree.exists_hubSet
#print axioms RTree.card_atlasEdge
#print axioms RTree.card_star
#print axioms RTree.star_disjoint
#print axioms RTree.card_hubEdges
#print axioms RTree.card_edges_off_hubs
#print axioms RTree.exists_hub_decomposition
#print axioms RTree.leaf_arms
#print axioms RTree.card_atlasEdge_leaves
#print axioms RTree.card_offHubEdges
#print axioms RTree.exists_hub_edge_partition
#print axioms RTree.pathOf_iposOfPath
#print axioms RTree.iposOfPath_pathOf
#print axioms RTree.exists_iposEquiv
#print axioms RTree.card_ipos_eq_card_ipaths
#print axioms RTree.iposDepth_iposOfPath
#print axioms RTree.card_iposEvenHubs_add_card_iposOddHubs
#print axioms RTree.ceil_half_le_max_ipos_class
#print axioms RTree.exists_hubSet_ipos
#print axioms RTree.card_hubEdgesIpos
#print axioms RTree.card_offHubEdgesIpos
#print axioms RTree.exists_hub_edge_partition_ipos
#print axioms RTree.exists_children_of_ipos
#print axioms RTree.three_mul_le_two_mul_sub_one
#print axioms RTree.exponent_bookkeeping
#print axioms RTree.moment_exponent
#print axioms RTree.not_parent_child_of_same_parity
#print axioms RTree.card_atlasLeaves
#print axioms RTree.leaf_arms_atlas
#print axioms RTree.leaf_arms_at_ipos
#print axioms RTree.exists_hub_structure
#print axioms RTree.check_six_two
#print axioms RTree.check_six_two_exponent
