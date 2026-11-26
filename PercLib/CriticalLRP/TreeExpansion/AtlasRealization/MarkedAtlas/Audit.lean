/- Independently rebuilt and verified at production revision
    eb9b71a3cf20a0fe9906271415f5b17efd80f5ad.
    Original scratch source is recorded below. -/
/- Standard-axiom audit of the finite marked atlas bound of Direction A. -/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.TwoLeaf

/-! Axiom audit.  Every one of these must use only `propext`, `Classical.choice`, `Quot.sound`. -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.MarkedAtlas.markPos_unique
#print axioms PercLib.CriticalLRP.MarkedAtlas.markDepth_le_card
#print axioms PercLib.CriticalLRP.MarkedAtlas.markedBase_subset_cover
#print axioms PercLib.CriticalLRP.MarkedAtlas.prob_markedBase_le_shapeSum
#print axioms PercLib.CriticalLRP.MarkedAtlas.sum_markDiag_eq_sum_markCoeff
#print axioms PercLib.CriticalLRP.MarkedAtlas.prob_markedBase_le_markCoeff
#print axioms PercLib.CriticalLRP.MarkedAtlas.prob_markedBase_le_markedBound
#print axioms PercLib.CriticalLRP.MarkedAtlas.markedBaseEvent_eq_image
#print axioms PercLib.CriticalLRP.MarkedAtlas.card_aedge_ltOn
#print axioms PercLib.CriticalLRP.MarkedAtlas.sum_prob_markedBase_le_markedBound
#print axioms PercLib.CriticalLRP.MarkedAtlas.pconn_self
#print axioms PercLib.CriticalLRP.MarkedAtlas.markedBound_p0
#print axioms PercLib.CriticalLRP.MarkedAtlas.prob_markedBase_p0
#print axioms PercLib.CriticalLRP.MarkedAtlas.prob_markedBase_le_pconn_p0
#print axioms PercLib.CriticalLRP.MarkedAtlas.prod_aedge_twoLeaf
#print axioms PercLib.CriticalLRP.MarkedAtlas.markDiag_twoLeaf
#print axioms PercLib.CriticalLRP.MarkedAtlas.eq_markShapeP1
#print axioms PercLib.CriticalLRP.MarkedAtlas.sum_markDiag_p1
#print axioms PercLib.CriticalLRP.MarkedAtlas.prob_markedBase_le_threePoint_p1
#print axioms PercLib.CriticalLRP.MarkedAtlas.sum_f_markDiag_p1
#print axioms PercLib.CriticalLRP.MarkedAtlas.sum_prob_markedBase_le_rowSum_p1
#print axioms PercLib.CriticalLRP.MarkedAtlas.markDepth_p1_eq_two
#print axioms PercLib.CriticalLRP.MarkedAtlas.markedBound_p1
#print axioms PercLib.CriticalLRP.MarkedAtlas.prob_markedBase_le_markedBound_p1
