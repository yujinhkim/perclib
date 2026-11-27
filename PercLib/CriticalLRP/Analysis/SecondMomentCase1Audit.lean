/-
Integrated and independently rebuilt from accepted Ultramath `smwyue9wx`, member `m1`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwyue9wx`, member `m1`, direction d1: axiom audit for the Case-1 packet.

Every declaration of `CaseOne.lean` is checked to depend only on the three standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`).  There is no `sorry`, `admit`,
`native_decide` or custom axiom in this directory, and no new definition is introduced
(the packet only states theorems about the existing `M.p2ExclError`, `M.p2Ebar`,
`M.cutMoment`, `M.connCubeMass`), so no `Defs.lean` accompanies it.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase1

/-! # Case 1 of Proposition I.4.15: axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.CaseOne

#print axioms cutMoment_four_mixed_le
#print axioms cutMoment_four_ne_top_of_two
#print axioms window_den_pos
#print axioms p2ExclError_le_caseOne
#print axioms eventually_window_ratio_le_rpow
#print axioms eventually_p2ExclError_le_rpow
#print axioms connCubeMass_ratio_le_caseOne
#print axioms connCubeMass_ratio_tendsto_zero_of_caseOne
#print axioms p2ExclError_tendsto_zero_of_caseOne
#print axioms integrableOn_abs_div_p2ExclError
#print axioms logarithmicallyIntegrable_p2ExclError
#print axioms logIntegrable_abs
#print axioms logIntegrable_of_eventually_abs_le
#print axioms abs_one_sub_mul_le
#print axioms logIntegrable_p2Ebar
#print axioms tendsto_div_two_of_caseOne
#print axioms regularlyVarying_two_of_caseOne
#print axioms p2Ebar_tendsto_zero_of_caseOne
#print axioms regularlyVarying_two_of_connCubeRatio_of_caseOne
#print axioms pow_one_add_le
#print axioms pow_one_sub_ge
#print axioms eventually_abs_ncard_mul_rpow_sub_one_le
#print axioms logIntegrable_cutE0
#print axioms logIntegrable_p2Ebar_of_caseOne
#print axioms tendsto_div_two_of_caseOne_reduced

end PercLib.CriticalLRP.CaseOne
