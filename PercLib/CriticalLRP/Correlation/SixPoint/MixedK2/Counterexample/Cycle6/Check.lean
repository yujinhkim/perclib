/-
Axiom audit for the `ZMod 6` counterexample.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Cycle6.Main

/-!
# Axiom audit for the translation-invariant `ZMod 6` counterexample
-/


set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.hpoint_fails_at
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.hubBound_bundle_false
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.hpoint_false
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.hq_stepProfile
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.eps_cube_le_law_conn_three
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.tau_le
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.conn_subset_arcs
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.reachable_crossing
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.jointP_le
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.hubStar_le_of_exp
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.hubStar_le_slot
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.slotK2_le
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.tsum_slotK2_le
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.num_lt
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.law_conn_le
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.cross_left_dec
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.cross_right_dec
#print axioms PercLib.CriticalLRP.Counterexample.Cycle6.eAt_eq_iff
