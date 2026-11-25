/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/Check.lean ; module path rewritten only.
The canonical lattice instantiation is audited after it.
-/

/-
Axiom audit for the direction-A development: every export must depend only on
`propext`, `Classical.choice` and `Quot.sound`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.Lattice

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.I417Example

#print axioms Tree5
#print axioms D2
#print axioms D3a
#print axioms D3b
#print axioms edgeFinset
#print axioms mem_edgeFinset

#print axioms bk_fin_ennreal
#print axioms tree5_le

#print axioms edgeFinset_disjoint_of_list_disjoint
#print axioms edges_disjoint_of_regions
#print axioms edges_disjoint_three
#print axioms mem_dropUntil_of_notMem_takeUntil
#print axioms mem_takeUntil_of_notMem_dropUntil
#print axioms tree5_mem_of_walks
#print axioms exists_two_level_branch

#print axioms threeLeaf_treeGraph

#print axioms tsum_comm4
#print axioms tsum_tsum_mul_fac
#print axioms tsum_tsum_mul_const
#print axioms famA_value
#print axioms famB_value
#print axioms famC_value
#print axioms jointSq_le

#print axioms connSet_comm
#print axioms measure_connSet_self
#print axioms tsum_T2_mul
#print axioms tsum_T3_mul
#print axioms T2_le_T3
#print axioms T3_le_T4
#print axioms markSet_le
#print axioms excess_le
#print axioms excess_le_two_four

#print axioms connSet_subset_disjOcc_self
#print axioms yInSet_subset_markSet
#print axioms prodSet_subset_tight
#print axioms measure_prodSet_le_tight
#print axioms twoCopy_moment_le_tight
#print axioms printed_le
#print axioms printed_le_lintegral
#print axioms printed_le_of_transitive
#print axioms source_le_two_four

#print axioms connects_permConfig_iff
#print axioms measure_connSet_perm
#print axioms meanVol_perm
#print axioms meanVol_eq_of_transitive

#print axioms latticeLongRange_I417_p21_printed

end PercLib.CriticalLRP.I417Example
