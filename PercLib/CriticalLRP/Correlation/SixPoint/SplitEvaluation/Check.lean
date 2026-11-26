/-
Axiom audit for the split-slot evaluations.

Swarm `smwxfstjy`, member `m2`, direction d3 (`REMAINING-SPLIT-EVALUATIONS`).

Every declaration below is checked to depend only on the three standard axioms
`propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`, no `admit`, no
`native_decide` and no custom axiom anywhere in this package.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation.Bridge

/-!
# Split evaluation and event bridges (`j = 0,5,6`)

The specified root placement is part of each evaluation. Other splits and the final moment assembly
remain open.-/


open Set MeasureTheory
open scoped ENNReal BigOperators

set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval

#print axioms peelZero
#print axioms peelFive
#print axioms peelSix
#print axioms reindexZero
#print axioms reindexFive
#print axioms reindexSix
#print axioms slotZero_tsum
#print axioms slotFive_tsum
#print axioms slotSix_tsum
#print axioms combSystem_zero_union_le
#print axioms combSystem_five_union_le
#print axioms combSystem_six_union_le
#print axioms zero_tsum_le
#print axioms five_tsum_le
#print axioms six_tsum_le
#print axioms slotZero_tsum_of_perm
#print axioms perm_swap_first_two
#print axioms nodup_swap_first_two
#print axioms combSystem_swap01
#print axioms one_tsum_le
#print axioms slotFive_tsum_of_perm
#print axioms slotSix_tsum_of_perm

end PercLib.CriticalLRP.SixPoint.SplitEval
