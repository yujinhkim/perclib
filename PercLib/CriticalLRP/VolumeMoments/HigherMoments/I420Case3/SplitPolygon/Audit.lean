/- Integrated from `.scratch/case3-split-draft/Audit.lean` at production base
`1266415364a0ad5f96cb689b36fbed1778a2af1f`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Assembly
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Eventually
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Model
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.ModelAssembly
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Tails
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.NearWindow
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.DirectEventually
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.DirectSource
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.MomentHom
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.TailLower
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.DirectTail
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.LowMoments

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
#print axioms PercLib.CriticalLRP.I420Case3.case3_i421_family_split_eventually
#print axioms PercLib.CriticalLRP.I420Case3.case3_i421_cutPoly_near_far
#print axioms PercLib.CriticalLRP.I420Case3.tendsto_nablaTail_rpow
#print axioms PercLib.CriticalLRP.I420Case3.power_nablaTail_limits
#print axioms PercLib.CriticalLRP.I420Case3.source_ball_card_pos
#print axioms PercLib.CriticalLRP.I420Case3.exists_source_near_far_ratio
#print axioms PercLib.CriticalLRP.I420Case3.exists_case3_i421_cutPoly_source
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAmid_of_i421_eventually
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_split_eventually
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source
#print axioms PercLib.CriticalLRP.I420Case3.powMomentAt_cutProb_perm
#print axioms PercLib.CriticalLRP.I420Case3.powMomentAt_cutProb_apply_eq_zero
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_finite
#print axioms PercLib.CriticalLRP.I420Case3.momOf_cutProb_eq_toReal_cutMoment
#print axioms PercLib.CriticalLRP.I420Case3.case3_hgm_of_tail
#print axioms PercLib.CriticalLRP.I420Case3.exists_case3_i421_cutPoly_source_of_tail
#print axioms PercLib.CriticalLRP.I420Case3.powMomentAt_ne_top_of_le_four
#print axioms PercLib.CriticalLRP.I420Case3.exists_case3_i421_cutPoly_source_of_tail_three
