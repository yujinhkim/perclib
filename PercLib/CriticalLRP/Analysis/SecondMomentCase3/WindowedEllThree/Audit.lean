/-
Axiom audit for the `smwzf17v9/m6` packet.

Every export below depends on the three standard Lean axioms only
(`propext`, `Classical.choice`, `Quot.sound`); there is no `sorry`, no `native_decide`,
no `sorryAx` and no custom axiom in this directory.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.NoGo
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Windowed
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Consumer
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Repaired
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Case3Windowed

set_option linter.style.longLine false

set_option linter.hashCommand false

@[expose] public section

/-! ## `Defs`: the windowed hypothesis and its relation to `hT3` -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowedEllThreeGap_of_perVertex

/-! ## `NoGo`: the per-vertex `ℓ = 3` input is refutable -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_polyK_three_diag_gt_const_mul_case3Driver
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_perVertexEllThreeGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3_polygon_bundle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3_polygon_bundle_of_cutMoment_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutTwoPoint_le_polyK_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_perVertexEllThreeGap_of_lower_bound

/-! ## `Windowed`: the windowed `ℓ = 3` bound at the Case-3 driver -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowPolyKThree_le_split
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.card_near_filter_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_half_card_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_card_rpow_half_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowPolyKThree_le_case3Driver_eventually
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_windowedEllThreeGap

/-! ## `Consumer`: the Case-3 numerator with the windowed input -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_of_windowedGap
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_of_perVertexGap'

/-! ## `Repaired`: the repaired bundle is satisfiable -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_repaired_case3_polygon_bundle

/-! ## `Case3Windowed`: Proposition I.4.15 Case 3 with the windowed input -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_windowed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_source
