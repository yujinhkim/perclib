/-
Axiom audit for the files of this directory (`smwxfstjy` member `m3`).

Every listed theorem must depend only on `propext`, `Classical.choice` and `Quot.sound`;
this file is compiled with `-DwarningAsError=true -DautoImplicit=false
-Dweak.linter.mathlibStandardSet=true` and fails on any other axiom and on any unfilled proof.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvents.Certificates

/-!
# Audit for the seven split certificates and their fivefold BK bounds
-/

set_option linter.hashCommand false
set_option linter.style.longLine false

open PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern

#print axioms usedStars_mem
#print axioms usedStars_lt
#print axioms residual_eq_usedSingles
#print axioms usedSingles_length
#print axioms nbrs_usedStars
#print axioms splitEvents_two

#print axioms combSystem_twoJointThree_one
#print axioms combSystem_twoJointThree_three
#print axioms combSystem_twoJointThree_four
#print axioms combSystem_certified
#print axioms law_combSystem_le
#print axioms law_combSystem_le_zero
#print axioms law_combSystem_le_one
#print axioms law_combSystem_le_two
#print axioms law_combSystem_le_three
#print axioms law_combSystem_le_four
#print axioms law_combSystem_le_five
#print axioms law_combSystem_le_six
