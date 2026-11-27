/-
Ultramath swarm `smwziumdb`, member `m6`, direction `d1`.

Axiom audit for every exported theorem of `Defs.lean` and `Main.lean`.  The accepted set is
`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, no custom axioms, no
`native_decide`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroCount.Main

/-! # Axiom audit for the branch-and-root tree count -/

set_option linter.hashCommand false

@[expose] public section

open PercLib.CriticalLRP.QZeroStarCount

#print axioms PercLib.CriticalLRP.QZeroStarCount.base_mem
#print axioms PercLib.CriticalLRP.QZeroStarCount.reps_eq_repsAux_succ
#print axioms PercLib.CriticalLRP.QZeroStarCount.repsAux_eq
#print axioms PercLib.CriticalLRP.QZeroStarCount.reps_eq
#print axioms PercLib.CriticalLRP.QZeroStarCount.leaves_reps
#print axioms PercLib.CriticalLRP.QZeroStarCount.leaves_reps_of
#print axioms PercLib.CriticalLRP.QZeroStarCount.sum_finset_factor
#print axioms PercLib.CriticalLRP.QZeroStarCount.TS_singleton'
#print axioms PercLib.CriticalLRP.QZeroStarCount.TS_eq_sum_reps
#print axioms PercLib.CriticalLRP.QZeroStarCount.TS_fin_four_eq_sum_reps
#print axioms PercLib.CriticalLRP.QZeroStarCount.sum_LT_fin_four
#print axioms PercLib.CriticalLRP.QZeroStarCount.card_reps_four
#print axioms PercLib.CriticalLRP.QZeroStarCount.leftmost_reps_four
#print axioms PercLib.CriticalLRP.QZeroStarCount.ell_two_card
#print axioms PercLib.CriticalLRP.QZeroStarCount.ell_three_card
#print axioms PercLib.CriticalLRP.QZeroStarCount.ell_four_card
#print axioms PercLib.CriticalLRP.QZeroStarCount.ell_mem
#print axioms PercLib.CriticalLRP.QZeroStarCount.shape_two_card
#print axioms PercLib.CriticalLRP.QZeroStarCount.shape_threeA_card
#print axioms PercLib.CriticalLRP.QZeroStarCount.shape_threeB_card
#print axioms PercLib.CriticalLRP.QZeroStarCount.shape_four_card
#print axioms PercLib.CriticalLRP.QZeroStarCount.shape_cases
#print axioms PercLib.CriticalLRP.QZeroStarCount.shape_two_iff_ell_two
#print axioms PercLib.CriticalLRP.QZeroStarCount.shape_three_iff_ell_three
#print axioms PercLib.CriticalLRP.QZeroStarCount.shape_four_iff_ell_four
#print axioms PercLib.CriticalLRP.QZeroStarCount.atlasEdges_length
#print axioms PercLib.CriticalLRP.QZeroStarCount.atlasDiagramSets_card
#print axioms PercLib.CriticalLRP.QZeroStarCount.atlasDiagramSets_iso_reps
#print axioms PercLib.CriticalLRP.QZeroStarCount.reps_iso_atlasDiagramSets
#print axioms PercLib.CriticalLRP.QZeroStarCount.atlasDiagramSets_pairwise
#print axioms PercLib.CriticalLRP.QZeroStarCount.repsDiagramSets_pairwise
#print axioms PercLib.CriticalLRP.QZeroStarCount.atlasIsoClosure_eq
