/-
Independently rebuilt and integrated from the accepted `smwx8o5tv/m2` artifact
`.ultramath/smwx8o5tv/m2/Q4`. Production integration revision:
`89f3b5eed8eb492ac975beb090e1d5e2fd9685ba`. Definitions, including `Diag`
and `baseDiag`, are confined to `Defs.lean`; the remaining files prove their
properties and the q=4 cover/BK bound, not its weighted moment evaluation.
-/
/-
Independently built for swarm `smwx8o5tv`, member `m2`, direction Q4-FINITE-COVER.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Four.Refined.Bound

/-!
# Axiom audit for the `q = 4` fresh cover and its BK bound

Every listed theorem depends only on the allowed axioms `propext`,
`Classical.choice`, and `Quot.sound`, and on nothing else. No `sorry`,
no `native_decide`, and no custom axiom.
-/

set_option linter.hashCommand false

open PercLib.CriticalLRP.I417FreshFour.Refined

#print axioms freshMark_subset_q4Shape
#print axioms freshMark_measure_le_q4
#print axioms shapeOfI_measure_le
#print axioms step
#print axioms baseDiag
#print axioms splitAt_left
#print axioms card_q4Index
#print axioms card_q4Branches
