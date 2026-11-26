/-
Independently rebuilt and integrated from the accepted `smwx9itnu/m2` artifact
`.ultramath/smwx9itnu/m2/Gen`. Production integration revision:
`8ae938fa49a73456688d438f25ef2441c282b2f4`.
The base split/diagram API is shared with `I417FreshFour.Refined` instead of
being duplicated.
-/
/-
Independently built for swarm `smwx9itnu`, member `m2`, direction GENERAL-Q-VECTOR-COVER.
No production files are modified; this module is read-only against production.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Iter.Bound

/-!
# Axiom audit for the general-`q` iterated first-hit fresh cover

Every public theorem of `Gen/Defs`, `Gen/Attach`, `Gen/Cover` and `Gen/Bound` is checked to rest on
at most `propext`, `Classical.choice` and `Quot.sound`.  There is no `sorry`, `admit`,
`native_decide` or custom axiom in the development.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.I417GenIter

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

#print axioms PercLib.CriticalLRP.I417GenIter.freshMark_subset_genShape
#print axioms PercLib.CriticalLRP.I417GenIter.exists_iter_diag
#print axioms PercLib.CriticalLRP.I417GenIter.step
#print axioms PercLib.CriticalLRP.I417GenIter.baseDiag
#print axioms PercLib.CriticalLRP.I417GenIter.splitAt_left
#print axioms PercLib.CriticalLRP.I417GenIter.Hist.first_leg_start
#print axioms PercLib.CriticalLRP.I417GenIter.shapeOfI_of_diag_legs
#print axioms PercLib.CriticalLRP.I417GenIter.shapeOfI_measure_le
#print axioms PercLib.CriticalLRP.I417GenIter.card_Idx
#print axioms PercLib.CriticalLRP.I417GenIter.card_genLegs
#print axioms PercLib.CriticalLRP.I417GenIter.card_histChoices
#print axioms PercLib.CriticalLRP.I417GenIter.card_histChoices_three
#print axioms PercLib.CriticalLRP.I417GenIter.card_histChoices_four
#print axioms PercLib.CriticalLRP.I417GenIter.exists_armEnum
#print axioms PercLib.CriticalLRP.I417GenIter.genShape_measure_le
#print axioms PercLib.CriticalLRP.I417GenIter.freshMark_measure_le_genShape
#print axioms PercLib.CriticalLRP.I417GenIter.card_genLegs_four
#print axioms PercLib.CriticalLRP.I417GenIter.freshMark_measure_le_freshPoly
#print axioms PercLib.CriticalLRP.I417GenIter.freshMark_subset_genShape_four
#print axioms PercLib.CriticalLRP.I417GenIter.freshMark_measure_le_poly
#print axioms PercLib.CriticalLRP.I417GenIter.tsum_freshMark_le_genShape
#print axioms PercLib.CriticalLRP.I417GenIter.freshMark_subset_genShape_five
#print axioms PercLib.CriticalLRP.I417GenIter.exists_freshMark_measure_le_genShape

end PercLib.CriticalLRP.I417GenIter
