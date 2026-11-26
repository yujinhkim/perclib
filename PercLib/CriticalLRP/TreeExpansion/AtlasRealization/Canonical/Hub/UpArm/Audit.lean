/-
Independently rebuilt from the prepared artifact of `smwx4z71g`, member `m1`.
Production integration revision: `5e579c30ee2c5caa2d151372f1929efd8ed587fb`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
-/
module
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.UpArm.ParentIncl

/-!
# Axiom audit for the parent-aware slot analysis of an atlas hub.
-/

open HubUpArm

namespace HubUpArm
set_option linter.hashCommand false

#print axioms isRootIpos_node_iff
#print axioms parentIPos_ne
#print axioms srcPos_hubUpEdge
#print axioms dstPos_hubUpEdge
#print axioms hubUpEdge_eq_parentDown
#print axioms hubUpSrc_eq_hubPos_iff

#print axioms hubStarJoint_arm_connects
#print axioms hubStarJoint_subset_threePoint
#print axioms hubStarJoint_subset_upPair
#print axioms hubStarJoint_subset_rootPair
#print axioms hubStarJoint_subset_parentPair
#print axioms edgeMeasure_hubStarJoint_le_jointP
#print axioms edgeMeasure_hubStarJoint_le_jointP_mul_tau
#print axioms canonAtlasEvent_subset_upPair

end HubUpArm
