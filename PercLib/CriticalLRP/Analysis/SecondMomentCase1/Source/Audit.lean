/-
Ultramath swarm `smwznoz6j`, member `m4`, direction `d5`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m4.
Production base `a42ae967cb8649dffa6f108a7a474602dd8a0d76`; reviewed scratch source `.scratch/review-smwznoz6j/m4/Audit.lean`.

# Axiom audit for the Case-1 packet

Every export of `Defs.lean` and `CaseOneNoRadial.lean` is checked here to depend only on the three
standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`.  There is no `sorry`,
`admit`, `native_decide`, `sorryAx` or custom axiom in either file.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase1.Source.Main

/-! # Axiom audit: Proposition I.4.15, Case 1 without radial inputs -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.FirstMomentUpperAt
#print axioms PercLib.CriticalLRP.CaseOne.eventually_window_ratio_le_rpow_of_firstMomentUpper
#print axioms PercLib.CriticalLRP.CaseOne.eventually_p2ExclError_le_rpow_of_firstMomentUpper
#print axioms PercLib.CriticalLRP.CaseOne.p2ExclError_tendsto_zero_of_firstMomentUpper
#print axioms PercLib.CriticalLRP.CaseOne.logarithmicallyIntegrable_p2ExclError_of_firstMomentUpper
#print axioms PercLib.CriticalLRP.CaseOne.tendsto_div_two_of_caseOne_no_ac
#print axioms PercLib.CriticalLRP.CaseOne.regularlyVarying_two_of_caseOne_no_ac
#print axioms PercLib.CriticalLRP.CaseOne.exists_cube_comparable_of_caseOne_no_ac
#print axioms PercLib.CriticalLRP.CaseOne.momentGap_of_caseOne_no_ac
#print axioms PercLib.CriticalLRP.CaseOne.firstMomentUpperAt_of_hP
#print axioms PercLib.CriticalLRP.CaseOne.eventually_p2ExclError_le_rpow_recovered
#print axioms PercLib.CriticalLRP.CaseOne.propositionI415_caseOne_no_ac
#print axioms PercLib.CriticalLRP.CaseOne.eventually_cutMoment_two_ne_top_of_hP
#print axioms PercLib.CriticalLRP.CaseOne.tendsto_div_two_of_caseOne_source
#print axioms PercLib.CriticalLRP.CaseOne.regularlyVarying_two_of_caseOne_source
#print axioms PercLib.CriticalLRP.CaseOne.propositionI415_caseOne_source
#print axioms PercLib.CriticalLRP.CaseOne.exists_cube_comparable_of_caseOne_source
#print axioms PercLib.CriticalLRP.CaseOne.momentGap_of_caseOne_source
