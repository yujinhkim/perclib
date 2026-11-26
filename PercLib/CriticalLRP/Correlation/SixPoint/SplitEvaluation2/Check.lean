/-
Coordinator audit of the first two additional slot evaluations.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.Defs

/-!
# Axiom audit for the two `j = 0` root-placement evaluations

No moment assembly or other split evaluation is asserted here.
-/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.slotU2_zero_tsum
#print axioms PercLib.CriticalLRP.SixPoint.SplitEval2.slotV2_zero_tsum
