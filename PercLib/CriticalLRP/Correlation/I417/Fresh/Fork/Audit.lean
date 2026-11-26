/- Coordinator's independent axiom audit of the integrated fork/slack package.
Production base: `d2734e7c030f377ae4642466daef7f78ff648cb8`. -/

module
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Fork.Slack

/-! Axiom audit for the fork witness, BK arm sum and conditional chain reduction. -/

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh.Q3

set_option linter.hashCommand false

#print axioms forkEvent_measure_le
#print axioms fresh_fork_three_le
#print axioms fresh_fork_le_forkBound
#print axioms ds_forkEvent
#print axioms q3_doubleStar_fork_not_chain
#print axioms chainTerm_const
#print axioms singleHub_le_chain
#print axioms hubAveraged_le_chain
#print axioms freshCombBound_of_hubMoment
#print axioms freshCombBound_three_of_hubMoment

end PercLib.CriticalLRP.I417Fresh.Q3
