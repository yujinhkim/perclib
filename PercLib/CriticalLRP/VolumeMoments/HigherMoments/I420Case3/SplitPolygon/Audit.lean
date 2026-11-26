/- Integrated from `.scratch/case3-split-draft/Audit.lean` at production base
`1266415364a0ad5f96cb689b36fbed1778a2af1f`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Assembly
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Model

/-! # Axiom audit for the split Case-3 interface -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I420Case3.HasSplitPolygonBound
#print axioms PercLib.CriticalLRP.I420Case3.HasPolygonBound.hasSplitPolygonBound
#print axioms PercLib.CriticalLRP.I420Case3.polygon_sum_le_split
#print axioms PercLib.CriticalLRP.I420Case3.prodFactor_le_mixedExcl_add_splitPolygon
#print axioms PercLib.CriticalLRP.I420Case3.discrepancy_toReal_le_splitPolygon
#print axioms PercLib.CriticalLRP.I420Case3.discR_le_splitPolygon
#print axioms PercLib.CriticalLRP.I420Case3.case3_i421_family_split
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_split
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_split_of_i417
#print axioms PercLib.CriticalLRP.I420Case3.sum_polyK_three_le_near_far
#print axioms PercLib.CriticalLRP.I420Case3.cutPoly_three_sum_le_near_far
#print axioms PercLib.CriticalLRP.I420Case3.exists_hasSplitPolygonBound_cutPoly_near_far
#print axioms PercLib.CriticalLRP.I420Case3.tendsto_near_far_factor
