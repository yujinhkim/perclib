/-
Axiom audit for the composed moment-gap bound, its basepoint normalization,
and the canonical long-range-lattice specializations.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Composition.Models

/-! # Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I417SummedClose.moment_gap_le_markedPairSum
#print axioms PercLib.CriticalLRP.I417SummedClose.markedPairSum_eq_markedGapPoly
#print axioms PercLib.CriticalLRP.I417SummedClose.moment_gap_le_markedGapPoly
#print axioms PercLib.CriticalLRP.I417SummedClose.moment_gap_le_markedGapPoly_of_transitive
#print axioms PercLib.CriticalLRP.I417SummedClose.moment_gap_le_markedGapPoly_basepoint
#print axioms
  PercLib.CriticalLRP.I417SummedClose.momentDiff_nonneg_basepoint_of_transitive
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_profile_transitive
#print axioms
  PercLib.CriticalLRP.TreeExpansion.latticeLongRange_moment_gap_le_markedGapPoly
#print axioms
  PercLib.CriticalLRP.TreeExpansion.latticeLongRange_momentDiff_nonneg_basepoint
