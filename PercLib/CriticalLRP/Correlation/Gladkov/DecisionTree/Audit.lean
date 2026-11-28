/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Axiom audit for the decision-tree amalgamation development. Every exported theorem must
rest on exactly `propext`, `Classical.choice` and `Quot.sound`.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.Main
public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.Examples
public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.AdaptiveExample
public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.FixedSet

/-!
# Axiom audit

Prints the axiom set of every exported theorem of the decision-tree development.
-/

set_option linter.hashCommand false

@[expose] public section

#print axioms PercLib.GladkovAmalgam.readN_treeConfig
#print axioms PercLib.GladkovAmalgam.readback_treeConfig
#print axioms PercLib.GladkovAmalgam.unamal_treeConfig
#print axioms PercLib.GladkovAmalgam.treeConfig_injective
#print axioms PercLib.GladkovAmalgam.treeConfig_unamal
#print axioms PercLib.GladkovAmalgam.fiber_treeConfig
#print axioms PercLib.GladkovAmalgam.treeConfig_eq_pairConfig_iff
#print axioms PercLib.GladkovAmalgam.prodBernoulli_singleton
#print axioms PercLib.GladkovAmalgam.prod_wt_treeConfig
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeConfig
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeConfig_atom
#print axioms PercLib.GladkovAmalgam.measure_eq_sum_finset
#print axioms PercLib.GladkovAmalgam.measure_eq_sum_filter
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeFirst_second_indep
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeFirst
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeSecond
#print axioms PercLib.GladkovAmalgam.map_treeConfig_pair
#print axioms PercLib.GladkovAmalgam.map_treeConfig
#print axioms PercLib.GladkovAmalgam.unamal_injective
#print axioms PercLib.GladkovAmalgam.consistent_twoEdgeTree
#print axioms PercLib.GladkovAmalgam.treeSet_twoEdgeTree_adaptiveOmega
#print axioms PercLib.GladkovAmalgam.not_selfDetermined_adaptive
#print axioms PercLib.GladkovAmalgam.prodBernoulli_twoEdgeTree
#print axioms PercLib.GladkovAmalgam.prodBernoulli_oneStep
#print axioms PercLib.GladkovAmalgam.treeSet_oneStep
#print axioms PercLib.GladkovAmalgam.treeSet_emptyTree
#print axioms PercLib.GladkovAmalgam.step_trace
#print axioms PercLib.GladkovAmalgam.exists_stable
#print axioms PercLib.GladkovAmalgam.treeSet_iff_class
#print axioms PercLib.GladkovAmalgam.consistent_listTree
#print axioms PercLib.GladkovAmalgam.treeSet_listTree
#print axioms PercLib.GladkovAmalgam.prodBernoulli_listTree
#print axioms PercLib.GladkovAmalgam.prodBernoulli_fixedSet
#print axioms PercLib.GladkovAmalgam.trace_listTree
#print axioms PercLib.GladkovAmalgam.runN_listTree
