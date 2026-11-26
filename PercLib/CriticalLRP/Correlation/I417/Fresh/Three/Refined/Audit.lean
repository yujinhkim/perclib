/-
Independently reviewed and integrated from the completed artifact `smwx6p0op/m1`
at `.ultramath/smwx6p0op/m1/M3Q`. Production integration revision:
`3cd318e5a37d0dc889f23bd3baf1b8884e651a27`. The coordinator uses the production
namespace and fully qualified imports; the proof covers `q = 3`, not arbitrary `q`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Three.Refined.Lattice

/-!
Independently built for swarm `smwx6p0op`, member `m1`, direction Q3-MARK-ON-PATH-COVER.

# Axiom audit

`#print axioms` on every public declaration of the development: the cover, the BK bound, the
summed fresh factor, and the generic six-walk assembly.  Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.
-/

set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshThree.Refined

#print axioms shapeOf_mem_of_walks
#print axioms edgeFinset_takeUntil_disjoint_dropUntil
#print axioms shapeOf_split
#print axioms shapeA0_subset
#print axioms shapeB3_subset
#print axioms freshMark_subset_shapeQ3
#print axioms measure_union8_le
#print axioms shapeOf_measure_le
#print axioms freshMark_measure_le_shapes
#print axioms tau_comm
#print axioms iterPow_two_comm
#print axioms tsum_three
#print axioms structA
#print axioms structB1
#print axioms structC2
#print axioms evalA0
#print axioms evalB3
#print axioms tsum_freshMark_le_refined
#print axioms freshThreeRefined
#print axioms tsum_freshMark_le_refined_gen
#print axioms shapeOf_mem_of_walks
#print axioms shapeA1_subset
#print axioms freshShapeSum
#print axioms tsum_finThree_snd
#print axioms moment_gap_three_le_refined
#print axioms moment_gap_three_le_refined_transitive
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_moment_gap_three_le_refined

end PercLib.CriticalLRP.I417FreshThree.Refined
