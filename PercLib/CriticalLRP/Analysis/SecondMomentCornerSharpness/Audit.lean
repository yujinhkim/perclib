/-
Axiom audit for the sharpness witnesses.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Expected: only `propext`, `Classical.choice`, `Quot.sound`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCornerSharpness.Main

/-!
# Axiom audit for the sharpness witnesses

Every theorem below is expected to depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

set_option linter.hashCommand false

@[expose] public section

open MeasureTheory Set Filter

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM4

#print axioms monotone_stepAt
#print axioms eqOn_stepAt_Icc_of_notMem
#print axioms absolutelyContinuousOnInterval_stepAt_of_notMem
#print axioms exists_stepAt_family_deficit
#print axioms not_absolutelyContinuousOnInterval_stepAt
#print axioms integral_identity_stepAt_cornerFree
#print axioms integral_identity_stepAt_fails
#print axioms hasDerivAt_stepAt_of_ne
#print axioms ae_hasDerivAt_stepAt
#print axioms ae_deriv_integrable_does_not_give_ac
#print axioms monotone_cornerFun
#print axioms continuous_cornerFun
#print axioms lipschitzWith_cornerFun
#print axioms absolutelyContinuousOnInterval_cornerFun
#print axioms not_differentiableAt_cornerFun_zero
#print axioms hasDerivAt_cornerFun_of_ne
#print axioms ae_hasDerivAt_cornerFun
#print axioms not_forall_hasDerivAt_cornerFun
#print axioms cornerFun_satisfies_gluing_hypotheses
#print axioms no_gluing_without_continuity
#print axioms no_corner_transfer_without_continuity
#print axioms no_pointwise_derivative_at_corner
#print axioms gluing_without_continuity_false
#print axioms corner_transfer_without_continuity_false
#print axioms pointwise_derivative_at_corner_false

end PercLib.CriticalLRP.Orchestration.SmwywszgoM4
