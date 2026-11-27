/-
Integrated and independently rebuilt from accepted Ultramath `smwytmnfc`, member `m2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwytmnfc`, member `m2`, direction d1: axiom audit.

Every declaration of `Defs.lean`, `Bounds.lean` and `Normalized.lean` is checked to depend only on
the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).  No `sorry`, `admit`,
`native_decide` or custom axiom occurs in this directory.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentError.Normalized

/-! # Second-moment error and normalized ODE interfaces: axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.SecondMomentError

#print axioms cE2_nonneg
#print axioms cE2_le
#print axioms cE2_mem_Icc

end PercLib.CriticalLRP.SecondMomentError

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms p2WindowProduct_ne_top
#print axioms p2WindowProduct_toReal
#print axioms one_le_cutMoment_one_toReal
#print axioms one_le_cutMoment_two_toReal
#print axioms ball_ncard_pos
#print axioms p2ExclError_nonneg
#print axioms p2ExclError_le_connCubeMass_div
#print axioms p2ExclError_mem_Icc
#print axioms p2ExclError_le_connCubeLin_div
#print axioms p2ExclError_le_fourth_div
#print axioms p2ExclError_eq_second_form
#print axioms p2ExclMass_eq_window_mul_one_sub
#print axioms p2Flux_eq_three_mul_exclMassQuad
#print axioms p2Flux_eq_fourteen
#print axioms p2H_normalizes
#print axioms p2Flux_eq_fifteen
#print axioms rhsScalarTwo_eq_p2Flux
#print axioms rhsScalarTwo_eq_fourteen
#print axioms rhsScalarTwo_eq_fifteen
#print axioms p2H_tendsto_zero_iff_hP
#print axioms p2H_tendsto_zero_of_hP
#print axioms cutMomentReal_two_eq
#print axioms one_sub_p2Ebar
#print axioms one_sub_cutE0
#print axioms p2Ebar_tendsto_zero
#print axioms p2ExclError_tendsto_zero_of_connCubeRatio
#print axioms p2ExclError_tendsto_zero_of_fourthRatio
#print axioms ratio_eventually_eq
#print axioms ratio_tendsto_one
#print axioms ae_hasDerivAt_linear
#print axioms regularlyVarying_two
#print axioms regularlyVarying_two_of_hP
#print axioms regularlyVarying_two_of_connCubeRatio
#print axioms regularlyVarying_two_of_hP_of_ae_deriv
#print axioms regularlyVarying_two_reduced
#print axioms tendsto_div_two
#print axioms tendsto_div_two_normalized
#print axioms tendsto_div_two_of_hP
#print axioms momOf_two_regularlyVarying

end PercLib.CriticalLRP.Orchestration.SourceModelData
