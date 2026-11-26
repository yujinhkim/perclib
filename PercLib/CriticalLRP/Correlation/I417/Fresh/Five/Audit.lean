/-
Axiom and scope audit for the `q = 5` moment composition (swarm `smwxcafk7`, member `m2`).
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Five.Moment

/-!
# Audit

Every named result of this directory is checked to depend only on Lean's standard axioms
`[propext, Classical.choice, Quot.sound]`.  Nothing here uses `sorry`, `admit`, `native_decide` or a
custom axiom.
-/

open PercLib.CriticalLRP

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I417FreshFive.Eval.hubArmSum_eq_meanVol
#print axioms PercLib.CriticalLRP.I417FreshFive.Eval.tsum_finFive_snd
#print axioms PercLib.CriticalLRP.I417FreshFive.Eval.moment_gap_five_le_eval_rowSum
#print axioms PercLib.CriticalLRP.I417FreshFive.Eval.moment_gap_five_le_eval
#print axioms PercLib.CriticalLRP.I417FreshFive.Eval.moment_gap_five_le_eval_transitive
#print axioms PercLib.CriticalLRP.I417FreshFive.Eval.factorCount_five
#print axioms PercLib.CriticalLRP.I417FreshFive.Eval.factorCount_five_all
#print axioms PercLib.CriticalLRP.I417FreshFive.Eval.pathPow_range_five
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_moment_gap_five_le_eval

-- the integrated `q = 5` fresh evaluation used by the moment composition
#print axioms PercLib.CriticalLRP.I417FreshFive.tsum_freshMark_le_profile_five
#print axioms PercLib.CriticalLRP.I417FreshFive.tsum_q5_le_profile
#print axioms PercLib.CriticalLRP.I417FreshFive.freshFiveEval_holds
#print axioms PercLib.CriticalLRP.I417FreshFive.freshMark_subset_q5Shape
#print axioms PercLib.CriticalLRP.I417FreshFive.freshMark_measure_le_q5
#print axioms PercLib.CriticalLRP.I417FreshFive.exists_diag_q5
#print axioms PercLib.CriticalLRP.I417FreshFive.ev_0
#print axioms PercLib.CriticalLRP.I417FreshFive.ev_383

-- the production inputs
#print axioms PercLib.CriticalLRP.I417Gen.moment_gap_tsub_le_marked
#print axioms PercLib.CriticalLRP.I417MarkedTransversal.jointPow_le_nonplane_markedDepth
