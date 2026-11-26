/- Independently reviewed exact-count proof from smwwtnhaw/m1, with a
strict fresh rebuild and standard-axiom audit at the current integration bank. -/
/-
Independent UltraMath work, swarm `smwwtnhaw`, member `m1`.
Production base `4c53bb5a8e76a4358a426adf71169b916b90f51f` (read-only package
`.scratch/critical-lrp-orchestration`), Lean 4.35.0.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.ExactCount.Exact

/-!
# Axiom audit for the exact child-swap orbit count

Every result below is expected to depend on exactly `[propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, `native_decide` or custom axiom is used in `OrbitCount/`.
-/

set_option linter.hashCommand false
set_option autoImplicit false

open PercLib.CriticalLRP.TreeExpansion

#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.peel_insertAt
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.posPath_inj
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.insertMap_injective
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.insertMap_bijective
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_LT_sum_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_LT_fin_succ_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_LT_fin_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_fin_succ_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_fin_eq_dfactorial
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_fin_zero
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_fin_zero_ne_M
#print PercLib.CriticalLRP.TreeExpansion.RTree.insertMap_injective
#print PercLib.CriticalLRP.TreeExpansion.RTree.card_LT_sum_eq
#print PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_fin_succ_eq
#print PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_fin_eq_dfactorial
#print PercLib.CriticalLRP.TreeExpansion.RTree.card_LT_fin_eq
