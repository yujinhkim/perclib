/- Independently rebuilt from `smwx3hvzx`, member `m1` finding f1.
Production integration revision: `c491c66109f24f38fa27cbccbcc52d11a14a8c33`.

Axiom audit for the hub-evaluation component of the `p = 3`, `k = 1` mixed moment bound.

Every declaration below is a theorem of the self-contained modules `HubJointEval/Defs.lean`,
`HubJointEval/Bridge.lean`, `HubJointEval/SourceDiag.lean`, `HubJointEval/Summation.lean` and
`HubJointEval/Assembly.lean`.  The audit prints the axioms used; only the three standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`) are acceptable.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Evaluation.Assembly
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Evaluation.Obstruction

/-!
# Axiom audit

Prints the axioms of every public theorem of the hub-evaluation component.
-/

set_option linter.hashCommand false

open HubJointEval

#print axioms disjFam_subset_of_isUpperSet
#print axioms hubArmJoint_subset_pair
#print axioms edgeMeasure_hubArmJoint_le_jointP
#print axioms edgeMeasure_hubArmJoint_le_prod
#print axioms hubStarJoint_subset_downPair
#print axioms edgeMeasure_hubStarJoint_le_jointP
#print axioms hubStarJoint_subset_downPair
#print axioms hubDiagJoint_eq_starPairEvent
#print axioms hubDiagJoint_subset_pair
#print axioms edgeMeasure_hubDiagJoint_le_jointP
#print axioms edgeMeasure_hubDiagJoint_le_hubSplitValue
#print axioms tau_row_sum
#print axioms hubPairSum_eq_secondMoment
#print axioms hubBlock_factor
#print axioms hubSplitSum_eq
#print axioms tsum_hubSplitEvent_le
#print axioms triple_le_hubSplitSum
#print axioms tsum_triple_hubSplit_eq
#print axioms third_moment_hub_le
#print axioms connects_oneEdgeConfig
#print axioms pair_mem_of_witness
#print axioms hubPairJoint_not_subset_hubArmJoint
#print axioms third_moment_hub_le'
