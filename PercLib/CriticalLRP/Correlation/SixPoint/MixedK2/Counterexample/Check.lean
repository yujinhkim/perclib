/-
Coordinator axiom audit for the independently rebuilt `smwxb4a1l/m3` Line6 result.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Main

/-!
# Axiom audit for the non-transitive `Fin 6` counterexample
-/

set_option linter.hashCommand false

open PercLib.CriticalLRP.Counterexample.Line6

#print axioms law_subset_lineEdges
#print axioms law_lineSupport
#print axioms law_congr_of_lineSupport
#print axioms reach_iff_seg
#print axioms seg_card
#print axioms exp_eight
#print axioms exp_seven_attained
#print axioms tau_line
#print axioms jointP_le_eps
#print axioms law_five
#print axioms hubStar_bound
#print axioms slotK2_bound
#print axioms tsum_slotK2_bound
#print axioms numeric
#print axioms hpoint_false
