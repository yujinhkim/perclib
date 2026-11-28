/-
Axiom audit for the random-revealed-set amalgamation modules. Every exported theorem must
rest on exactly `propext`, `Classical.choice` and `Quot.sound`.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.RandomAmalgam
public import PercLib.CriticalLRP.Correlation.Gladkov.RandomAmalgamExample
public import PercLib.CriticalLRP.Correlation.Gladkov.RandomAmalgamCounterexample

/-!
# Axiom audit

Prints the axiom set of every exported theorem of the three random-amalgamation modules.
-/

set_option linter.hashCommand false

@[expose] public section

open PercLib.GladkovAmalgam

#print axioms PercLib.GladkovAmalgam.prodBernoulli_random_amalgam_indep
#print axioms PercLib.GladkovAmalgam.prodBernoulli_random_amalFirst
#print axioms PercLib.GladkovAmalgam.prodBernoulli_random_amalSecond
#print axioms PercLib.GladkovAmalgam.map_random_amalFirst
#print axioms PercLib.GladkovAmalgam.random_amalgam_indep_const
#print axioms PercLib.GladkovAmalgam.idx_flipConfig_eq
#print axioms PercLib.GladkovAmalgam.preimage_fiber_flipConfig
#print axioms PercLib.GladkovAmalgam.measurable_amalFirstRand
#print axioms PercLib.GladkovAmalgam.measurable_amalSecondRand
#print axioms PercLib.GladkovAmalgam.step_selfDetermined
#print axioms PercLib.GladkovAmalgam.step_random_amalgam_indep
#print axioms PercLib.GladkovAmalgam.map_random_amalgam_prod
#print axioms PercLib.GladkovAmalgam.badIdx_not_selfDetermined
#print axioms PercLib.GladkovAmalgam.treeIdx_not_selfDetermined
#print axioms PercLib.GladkovAmalgam.bad_second_mass
#print axioms PercLib.GladkovAmalgam.not_marginal_automatic
