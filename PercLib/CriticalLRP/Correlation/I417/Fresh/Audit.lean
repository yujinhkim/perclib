/- Integrated from independently rebuilt Ultramath work.
Production base 7a04599a899ac160fd051de07e5a0ef98d771674.
Scratch source: ../../.ultramath/smwvlmbqa/m4/Audit.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Main

/-!
Axiom audit for the fresh-side bounds.
-/

set_option linter.hashCommand false

open PercLib.CriticalLRP.I417Fresh

#print axioms mem_hubStar_iff
#print axioms mem_armStar_iff
#print axioms connSet_swap
#print axioms freshMark_subset_hubStar
#print axioms isUpperSet_hubStar
#print axioms finiteWitness_hubStar
#print axioms freshMark_measure_le_twoArm
#print axioms freshMark_measure_le_oneHub
#print axioms fresh_factor_one_le
#print axioms fresh_factor_le_hubStar
#print axioms fresh_factor_le_hubStar_apply
#print axioms freshCombBound_one
#print axioms freshCombBound_holds_one
