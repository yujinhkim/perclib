/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Swarm smwwr4usj / member m1: standard-axiom audit of the hub-regrouping layer.

Every theorem below is checked to rest on at most `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`/`admit`/`native_decide`, no new axioms, no opaque replacement predicates.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Hub.StarEnds
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Hub.Probability

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.Real.mem_hubStarAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.mem_hubAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.mem_offHubAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.card_hubStarAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.card_hubAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.card_offHubAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.hubAEdges_union_offHubAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.disjoint_hubAEdges_offHubAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.disjoint_hubStarAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.hubAEdges_empty
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.offHubAEdges_empty
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.hubSplitConnProd_empty
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prod_hubStarAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prod_hubAEdges
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.atlasConnProd_eq_hubSplit
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.disjOcc_restrict
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.diagEvent_subset_hubStarJoint
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.diagEvent_subset_hubStarAllJoint
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_hubStarJoint_le
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_hubStarAllJoint_le
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_hubStarAllJoint_le_hubSplit
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_diagEvent_le_atlasConnProd
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_diagEvent_le_hubSplit
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.exists_hub_product_bound
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_le_sum_shapes_hubSplit
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.childPos_iposOfPath_app
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.atlasEdgeEquiv_inl
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.upEdge_dstPos
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.hubStarAEdges_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.hubStarAEdges_incident
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.rootEdge_mem_hubStarAEdges
