/-
Axiom audit for the files of this directory (`smwxenel0` member `m2`).

Every listed theorem must depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitPattern.Regroup
public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointThree.Regroup

/-!
# Audit for the split-position classification and three partial split certificates
-/

set_option linter.hashCommand false
set_option linter.style.longLine false

open PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern

#print axioms indepPairs_eq_table
#print axioms indepPairs_length
#print axioms internal_class_sizes
#print axioms larger_class_at_least_two
#print axioms classPairs_subset_indep
#print axioms classPairs_length
#print axioms star_partition
#print axioms production_pattern
#print axioms production_pattern_events
#print axioms arms_in_splitEdges
#print axioms split_arm_halves
#print axioms edge_budget
#print axioms double_factorial_five
#print axioms nestProd_eq
#print axioms target_five_two
#print axioms walkEdges_reverse
#print axioms StarCert.cert_mem
#print axioms fiveGroup_of_two_stars
#print axioms combSystem_twoJointThree_zero
#print axioms combSystem_twoJointThree_five
#print axioms combSystem_twoJointThree_six
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.combSystem_twoJointThree
