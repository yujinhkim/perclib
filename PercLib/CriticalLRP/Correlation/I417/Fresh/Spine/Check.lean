/-
Axiom audit for the independently reviewed `smwxcafk7/m1` spine infrastructure.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Spine.Profile

/-!
# Axiom audit for the analytic spine evaluation infrastructure

This checks the summation lemmas, not the remaining `Hist.legs`-to-spine bridge.
-/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I417FreshGenSpine.Hang.val_eq_pow
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spineVal_eq
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spineVal_eq_normal
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spineVal_eq_kernel
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spineVal_congr_size
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spine_aggregate
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spine_aggregate_genFreshProfile
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.genFreshProfile_four
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.genFreshProfile_five
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spineVal_four_profile_first
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spineVal_four_profile_last
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spineVal_hub
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spineVal_q5
#print axioms PercLib.CriticalLRP.I417FreshGenSpine.spineVal_q4
