/- Independently rebuilt axiom audit for `smwx2gpeq`, member `m1`.
Production integration revision: `4a0f1d2a3c823f8e636a9296a0a909362bdee4d7`.

Every public result of the canonical-hub layer is printed with `#print axioms`.  The expected
answer for every line is `[propext, Classical.choice, Quot.sound]` (or a subset), i.e. Lean's
three standard axioms and nothing else: no `sorry`, no `admit`, no `native_decide`, no custom
axiom, no `Lean.ofReduceBool`.  The audit is run with

  lean -DwarningAsError=true -DautoImplicit=false -Dweak.linter.mathlibStandardSet=true \
       -o CanonHub/Audit.olean CanonHub/Audit.lean

so that a `sorry` anywhere in the dependency cone is a hard error before the audit is even read.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Main
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Marked

/-!
# Axiom audit of the canonical hub-regrouping layer

Definitions, the witness-level restriction, the regrouping algebra, the BK steps, the hub
selector and the label-event consumer, in that order.
-/

set_option linter.hashCommand false

/-! ## Definitions -/

#print axioms CanonAtlas.atlasConnEvent
#print axioms CanonAtlas.hubStarJoint
#print axioms CanonAtlas.hubAllJoint
#print axioms CanonAtlas.offHubJoint
#print axioms CanonAtlas.atlasEdgeProd
#print axioms CanonAtlas.hubStarProd
#print axioms CanonAtlas.offHubProd
#print axioms CanonAtlas.hubSplitProd

/-! ## The witness-level restriction -/

#print axioms CanonAtlas.mem_atlasConnEvent
#print axioms CanonAtlas.disjFam_subtype
#print axioms CanonAtlas.disjFam_subtype_of_subset
#print axioms CanonAtlas.isCanonRealization_restrictFam
#print axioms CanonAtlas.canonAtlasEvent_subset_hubStarJoint
#print axioms CanonAtlas.canonAtlasEvent_subset_hubAllJoint
#print axioms CanonAtlas.canonAtlasEvent_subset_hubAllJoint_inter_offHubJoint
#print axioms CanonAtlas.hubAllJoint_subset_hubStarJoint

/-! ## The regrouping algebra -/

#print axioms CanonAtlas.prod_hubStarAEdges_gen
#print axioms CanonAtlas.prod_hubAEdges_gen

/-! ## BK and the product regrouping -/

#print axioms CanonAtlas.edgeMeasure_hubStarJoint_le
#print axioms CanonAtlas.edgeMeasure_hubAllJoint_le
#print axioms CanonAtlas.edgeMeasure_offHubJoint_le
#print axioms CanonAtlas.edgeMeasure_hubAllJoint_le_hubSplit
#print axioms CanonAtlas.edgeMeasure_canonAtlasEvent_le_atlasEdgeProd
#print axioms CanonAtlas.atlasEdgeProd_eq_hubSplit
#print axioms CanonAtlas.hubSplitProd_empty
#print axioms CanonAtlas.edgeMeasure_canonAtlasEvent_le_hubSplit

/-! ## The hub selector and the consumers -/

#print axioms CanonAtlas.exists_canonHub_bound
#print axioms CanonAtlas.exists_hubSelection
#print axioms CanonAtlas.edgeMeasure_labelEvent_le_tsum_hubSplit_of_selection
#print axioms CanonAtlas.edgeMeasure_labelEvent_le_tsum_hubSplit

/-! ## The marked joint moment -/

#print axioms CanonAtlas.markedHubBound
#print axioms CanonAtlas.jointPow_le_markedHubBound
