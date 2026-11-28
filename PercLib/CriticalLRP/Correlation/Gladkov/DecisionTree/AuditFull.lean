/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Axiom audit of every theorem of the decision-tree development.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.FixedSet
public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.Examples
public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.AdaptiveExample

/-!
# Full axiom audit

Every theorem of `DecisionTree.Defs`, `Main`, `Examples`, `AdaptiveExample` and
`FixedSet` must rest on subsets of `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option linter.hashCommand false

@[expose] public section

#print axioms PercLib.GladkovAmalgam.adaptiveIdx_omega
#print axioms PercLib.GladkovAmalgam.adaptiveSfam_omega
#print axioms PercLib.GladkovAmalgam.bitOf_congr
#print axioms PercLib.GladkovAmalgam.bitOf_eq_false
#print axioms PercLib.GladkovAmalgam.bitOf_eq_of_iff
#print axioms PercLib.GladkovAmalgam.bitOf_eq_true
#print axioms PercLib.GladkovAmalgam.bit_congr
#print axioms PercLib.GladkovAmalgam.bit_eq_bitOf
#print axioms PercLib.GladkovAmalgam.bit_eq_false
#print axioms PercLib.GladkovAmalgam.bit_eq_of_iff
#print axioms PercLib.GladkovAmalgam.bit_eq_true
#print axioms PercLib.GladkovAmalgam.consistent_emptyTree
#print axioms PercLib.GladkovAmalgam.consistent_listTree
#print axioms PercLib.GladkovAmalgam.consistent_of_strong
#print axioms PercLib.GladkovAmalgam.consistent_oneStep
#print axioms PercLib.GladkovAmalgam.consistent_twoEdgeTree
#print axioms PercLib.GladkovAmalgam.edgeInj_of_edgesNodup
#print axioms PercLib.GladkovAmalgam.edgesNodup_step
#print axioms PercLib.GladkovAmalgam.edges_cover_of_length
#print axioms PercLib.GladkovAmalgam.exists_stable
#print axioms PercLib.GladkovAmalgam.fiber_treeConfig
#print axioms PercLib.GladkovAmalgam.getElem_not_mem_take
#print axioms PercLib.GladkovAmalgam.length_runN_le
#print axioms PercLib.GladkovAmalgam.length_runN_le_card
#print axioms PercLib.GladkovAmalgam.length_runN_of_unstable
#print axioms PercLib.GladkovAmalgam.length_step_le
#print axioms PercLib.GladkovAmalgam.length_step_of_ne
#print axioms PercLib.GladkovAmalgam.listTree_of_getElem?
#print axioms PercLib.GladkovAmalgam.listTree_of_le
#print axioms PercLib.GladkovAmalgam.map_treeConfig
#print axioms PercLib.GladkovAmalgam.map_treeConfig_pair
#print axioms PercLib.GladkovAmalgam.measurable_treeConfig
#print axioms PercLib.GladkovAmalgam.measurable_treeFirst
#print axioms PercLib.GladkovAmalgam.measurable_treePair
#print axioms PercLib.GladkovAmalgam.measurable_treeSecond
#print axioms PercLib.GladkovAmalgam.measure_eq_sum_filter
#print axioms PercLib.GladkovAmalgam.measure_eq_sum_finset
#print axioms PercLib.GladkovAmalgam.mem_pairConfig_false
#print axioms PercLib.GladkovAmalgam.mem_pairConfig_true
#print axioms PercLib.GladkovAmalgam.mem_treeConfig_of_mem
#print axioms PercLib.GladkovAmalgam.mem_treeConfig_of_not_mem
#print axioms PercLib.GladkovAmalgam.not_mem_treeSet_of_not_mem
#print axioms PercLib.GladkovAmalgam.not_selfDetermined_adaptive
#print axioms PercLib.GladkovAmalgam.not_selfDetermined_twoEdgeTree
#print axioms PercLib.GladkovAmalgam.prefix_runN
#print axioms PercLib.GladkovAmalgam.prefix_runN_succ
#print axioms PercLib.GladkovAmalgam.prefix_step
#print axioms PercLib.GladkovAmalgam.prodBernoulli_emptyTree
#print axioms PercLib.GladkovAmalgam.prodBernoulli_fixedSet
#print axioms PercLib.GladkovAmalgam.prodBernoulli_listTree
#print axioms PercLib.GladkovAmalgam.prodBernoulli_oneStep
#print axioms PercLib.GladkovAmalgam.prodBernoulli_singleton
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeConfig
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeConfig_atom
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeFirst
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeFirst_second_indep
#print axioms PercLib.GladkovAmalgam.prodBernoulli_treeSecond
#print axioms PercLib.GladkovAmalgam.prodBernoulli_twoEdgeTree
#print axioms PercLib.GladkovAmalgam.prod_wt_pairConfig
#print axioms PercLib.GladkovAmalgam.prod_wt_treeConfig
#print axioms PercLib.GladkovAmalgam.readN_succ
#print axioms PercLib.GladkovAmalgam.readN_treeConfig
#print axioms PercLib.GladkovAmalgam.readSet_treeConfig
#print axioms PercLib.GladkovAmalgam.readStep_of_none
#print axioms PercLib.GladkovAmalgam.readStep_of_some
#print axioms PercLib.GladkovAmalgam.readback_treeConfig
#print axioms PercLib.GladkovAmalgam.runN_edgesNodup
#print axioms PercLib.GladkovAmalgam.runN_emptyTree
#print axioms PercLib.GladkovAmalgam.runN_eq_of_stable
#print axioms PercLib.GladkovAmalgam.runN_listTree
#print axioms PercLib.GladkovAmalgam.runN_oneStep
#print axioms PercLib.GladkovAmalgam.runN_succ
#print axioms PercLib.GladkovAmalgam.step_of_none
#print axioms PercLib.GladkovAmalgam.step_of_some
#print axioms PercLib.GladkovAmalgam.step_trace
#print axioms PercLib.GladkovAmalgam.trace_emptyTree
#print axioms PercLib.GladkovAmalgam.trace_listTree
#print axioms PercLib.GladkovAmalgam.trace_oneStep
#print axioms PercLib.GladkovAmalgam.trace_twoEdgeTree_adaptiveOmega
#print axioms PercLib.GladkovAmalgam.treeConfig_eq_pairConfig_iff
#print axioms PercLib.GladkovAmalgam.treeConfig_injective
#print axioms PercLib.GladkovAmalgam.treeConfig_unamal
#print axioms PercLib.GladkovAmalgam.treeFirst_emptyTree
#print axioms PercLib.GladkovAmalgam.treeFirst_listTree
#print axioms PercLib.GladkovAmalgam.treeFirst_oneStep
#print axioms PercLib.GladkovAmalgam.treeSecond_emptyTree
#print axioms PercLib.GladkovAmalgam.treeSecond_listTree
#print axioms PercLib.GladkovAmalgam.treeSecond_oneStep
#print axioms PercLib.GladkovAmalgam.treeSet_emptyTree
#print axioms PercLib.GladkovAmalgam.treeSet_iff_class
#print axioms PercLib.GladkovAmalgam.treeSet_listTree
#print axioms PercLib.GladkovAmalgam.treeSet_oneStep
#print axioms PercLib.GladkovAmalgam.treeSet_twoEdgeTree_adaptiveOmega
#print axioms PercLib.GladkovAmalgam.unamal_injective
#print axioms PercLib.GladkovAmalgam.unamal_treeConfig
#print axioms PercLib.GladkovAmalgam.wt_twoProfile_eq
#print axioms PercLib.GladkovAmalgam.wt_twoProfile_fst
#print axioms PercLib.GladkovAmalgam.wt_twoProfile_snd
