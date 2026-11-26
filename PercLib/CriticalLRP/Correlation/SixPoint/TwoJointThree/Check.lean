/-
Coordinator axiom audit for the middle-split two-joint certificate.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointThree.Bound

/-!
# Axiom audit for one middle `CombSystem` split

This does not assert completion of all splits or a second-moment product evaluation.
-/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.twoJointThree_le
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.combSystem_twoJointThree
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.combSystem_twoJointThree_le
