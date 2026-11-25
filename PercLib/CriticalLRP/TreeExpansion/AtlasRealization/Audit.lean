/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m4/.
-/

/- Standard-axiom audit of the covering theorem and its probabilistic consumers. -/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Example

/-! Axiom audit for the Atlas realization and probabilistic consumer. -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.Real.exists_split
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.exists_realization
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.card_aedge
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.bk_disjOcc
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.diagEvent_eq_disjOcc
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_diagEvent_le
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.cover_union
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.prob_le_sum_shapes
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.srcPos_eq_dstPos_of_wit_eq_empty
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.ex_realization
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.ex_cover
#print axioms PercLib.CriticalLRP.TreeExpansion.Real.card_aedge_of_isLabelledShape
