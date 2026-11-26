/-
Independently reviewed and integrated from the partial artifact
`.ultramath/smwx6p0op/m3/HubEval`. Production integration revision:
`57e71d7ca447d7d83bfa761bb296fde27f6eb970`. This is a concrete one-shape
hub evaluation, not a general mixed-moment theorem.
-/
/-
Axiom audit for the `t3` one-hub block.

Independently built for swarm `smwx6p0op`, member `m3`, direction HUB-EVALUATED-BLOCK.

Every declaration of this development is checked to depend only on `propext`,
`Classical.choice` and `Quot.sound`.  No `sorry`, `admit`, `native_decide`, custom axiom or
hidden moment/transitivity input occurs in `Defs.lean`, `Assembly.lean` or `Summed.lean`; the two
translation-invariance statements carry their hypothesis explicitly.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Block.Summed

/-!
# Axiom audit
-/

@[expose] public section

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.t3
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.hubI
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.innerI
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.childPos_hub_false
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.childPos_hub_true
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.childPos_inner_false
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.childPos_inner_true
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.upEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.hubFalseEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.hubTrueEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armSlot
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armSlot_apply
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armSlot_zero
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armSlot_one
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armSlot_two
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.hubSlots
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.hubBlockValue
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.leafSumBlock
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.pinnedHubPairSum
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armSum
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armSlot_apply_base
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.hubStarAEdges_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.offHubAEdges_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.isRootIpos_hubI
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.hubUpSrc_hubI
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.srcPos_upEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.dstPos_upEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.srcPos_hubFalseEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.dstPos_hubFalseEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armEdge_ne_upEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armEdge_ne_hubFalseEdge
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armEdge_injective
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.canonAtlasEvent_subset_hubSlots
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.isUpperSet_hubSlots
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.finiteWitness_hubSlots
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.edgeMeasure_canonAtlasEvent_le_hubBlock
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.hubBlockValue_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.hubBlockValue_leaf
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.tsum_tsum_tsum_mul_prod
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.tsum_hubBlockValue
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.tsum_atlasValue_le_block
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.armSum_eq_of_const_rowSum
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.tsum_atlasValue_le_const
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.pinnedHubPairSum_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.tsum_tau_mul_pinnedHubPairSum
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.one_le_pinnedHubPairSum
#print axioms PercLib.CriticalLRP.TreeExpansion.HubEval.tsum_pinnedHubPairSum_eq_top
