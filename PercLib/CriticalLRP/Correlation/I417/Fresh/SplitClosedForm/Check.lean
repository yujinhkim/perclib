/-
Axiom audit for the closed-form iterated split weight (`CLOSED-FORM-SPLIT-WEIGHT`, `smwxenel0/m3`).
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.SplitClosedForm.Chain

/-!
# Axiom audit for the closed-form iterated split weight (`CLOSED-FORM-SPLIT-WEIGHT`, `smwxenel0/m3`)
-/

set_option linter.hashCommand false

open PercLib.CriticalLRP.I417SplitClosedForm

#print axioms chainM_eq_succ
#print axioms chainE_eq_succ
#print axioms chainM_pos
#print axioms pow_add_four
#print axioms splitWt_slotW_self
#print axioms slotW_step
#print axioms slotW_top
#print axioms sum_idx_succ_eq
#print axioms sum_chainE_add_chainM
