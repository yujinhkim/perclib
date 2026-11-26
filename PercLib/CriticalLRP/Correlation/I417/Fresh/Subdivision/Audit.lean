/-
Independently rebuilt and integrated from the accepted `smwx6p0op/m2` artifact
`.ultramath/smwx6p0op/m2/GQDepth`. Production integration revision:
`c83993396c566d21a0abe4051ed84dd6dab6093e`. The coordinator uses the production
namespace and fully qualified imports; this package is diagram infrastructure,
not an event-cover theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Instances
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Family
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.MarkSum

/-!
Independently built for swarm `smwx6p0op`, member `m2`, direction DEPTH-RANGE-I417.

# Axiom audit

Every declaration below must depend only on `propext`, `Classical.choice`, `Quot.sound`.  There is
no `sorry`, no `admit`, no `native_decide` and no custom axiom anywhere in the development; the only
hypothesis used by the value theorem is the constant row sum `χ` of the kernel, and the only
probabilistic input is production's already-checked `I417Base.tsum_wtE_marked` /
`I417Base.pathW_eq_iterPow` / `I417FreshTwo.iterPow_add_right` and the marked-count vanishings in
`I417MarkedPerDepth` / `I417MarkedTransversal`.  `composed_family_le` is the finite
coefficient-weighted diagram bound.
-/

open scoped ENNReal NNReal

set_option linter.hashCommand false
set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh.Subdivision

variable {V : Type*} [Countable V] [DecidableEq V]

#print axioms treeTot_eq
#print axioms iterPow_one
#print axioms iterPow_two
#print axioms subW_eq
#print axioms subW_eq_subMono
#print axioms subW_depth_le_numLeaves
#print axioms subMono_range
#print axioms subW_level_range
#print axioms base_marked_depth_range
#print axioms source_path_range
#print axioms source_edge_count
#print axioms fresh_family_by_depth
#print axioms iterPow_mul_le
#print axioms marked_fresh_le
#print axioms composed_depth_range
#print axioms combTree_numLeaves
#print axioms combTree_depth_deep
#print axioms comb_subW_max
#print axioms twoLeaf_depth_fst
#print axioms subW_two_leaf_depth_one
#print axioms subW_two_leaf_depth_two
#print axioms subW_two_leaf_shapeA
#print axioms subW_two_leaf_shapeB
#print axioms threeLeaf_depth_deep
#print axioms subW_three_leaf_depth_one
#print axioms subW_three_leaf_depth_two
#print axioms subW_three_leaf_depth_three
#print axioms composed_family_le
#print axioms marked_value_eq
#print axioms tsum_marked_fresh_eq
#print axioms tsum_marked_fresh_eq_two

end PercLib.CriticalLRP.I417Fresh.Subdivision
