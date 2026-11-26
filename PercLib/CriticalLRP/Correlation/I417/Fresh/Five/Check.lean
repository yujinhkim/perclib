/-
Coordinator axiom audit for the independently rebuilt `smwxb4a1l/m1` Q5 result.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Five.Summed

/-!
# Axiom audit for the finite `q = 5` fresh evaluation

The global production audit separately checks every declaration, including all 384 branch lemmas.
-/

set_option linter.hashCommand false

open PercLib.CriticalLRP.I417FreshFive

#print axioms round_q5
#print axioms exists_diag_q5
#print axioms freshMark_subset_q5Shape
#print axioms freshMark_measure_le_q5
#print axioms tsum_q5_le_profile
#print axioms tsum_freshMark_le_profile_five
#print axioms freshFiveEval_holds
#print axioms ev_0
#print axioms ev_191
#print axioms ev_383
