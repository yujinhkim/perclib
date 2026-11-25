/- Audit of the independently reviewed two-arm fresh bound. -/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Main

/-!
Axiom audit for the two-arm fresh-chain bound and its q = 2 consumers.
-/

set_option linter.hashCommand false
set_option linter.style.longLine false
#print axioms PercLib.CriticalLRP.I417Fresh.freshCombBound_two
#print axioms PercLib.CriticalLRP.I417Fresh.tsum_sTerm2_eq_sTerm3
#print axioms PercLib.CriticalLRP.I417Fresh.sTerms_le_chainTerm
#print axioms PercLib.CriticalLRP.I417Fresh.hubStarChain_two
#print axioms PercLib.CriticalLRP.I417Fresh.twoCopy_moment_le_marked_two
#print axioms PercLib.CriticalLRP.I417Fresh.moment_gap_tsub_le_marked_two
