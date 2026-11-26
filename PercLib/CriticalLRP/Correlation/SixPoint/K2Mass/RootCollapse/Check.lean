/-
Swarm `smwxii2d9`, member `m3`, direction `d1` (`ROOT-CLASS-COLLAPSE`).

Axiom audit for the root-class collapse.  Every declaration below must depend only on
`propext`, `Classical.choice` and `Quot.sound`: the collapse is a pure reindexing of
`ℝ≥0∞` sums (`SixPoint.TwoJointEval.tsum_fin5_perm`) plus `decide`-checked permutations of
`Fin 5`, and the fifth-moment bounds additionally use the `ℝ≥0∞` BK inequality already in
production.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.K2Mass.RootCollapse.Main

/-! Axiom audit for the root-class collapse. -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeVec_lift5_eq_slotVec
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeMass_eq_leafMass
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal_eq_shapeTotal5
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal5_eq_of_coordPerm
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal5_rootSlot0
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal5_rootSlot2
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal_rootSlot0
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal_rootSlot2
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal_eq_rootSlot
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal_eq_rootSlot_if
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.rootClass_collapse
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.shapeTotal_rootSlot_mid_le
#print axioms
  PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.fifth_moment_k2_le_of_rootSlot_bounds
#print axioms
  PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.tsum_shapeTotal_eq_rootClass
#print axioms
  PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.fifth_moment_k2_le_of_rootSlot_all_bounds
