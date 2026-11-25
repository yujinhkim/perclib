/- Production axiom audit for the polygon analytic assembly. -/
module

/-
Axiom audit for direction C of swarm `smwqozn0q` (member m3).

Build (see `build.sh`):
```
cd <package worktree>
LP="$(lake env printenv LEAN_PATH)"
cd <this dir>
LEAN_PATH="$LP"     lean -DwarningAsError=true -o Core.olean Core.lean
LEAN_PATH=".:$LP"   lean -DwarningAsError=true -o Source.olean Source.lean
LEAN_PATH=".:$LP"   lean -DwarningAsError=true -o Witness.olean Witness.lean
LEAN_PATH=".:$LP"   lean -DwarningAsError=true Check.lean
```
-/
public import PercLib.CriticalLRP.Analysis.Polygon.Core
public import PercLib.CriticalLRP.Analysis.Polygon.Model
public import PercLib.CriticalLRP.Analysis.Polygon.Witness
public import PercLib.CriticalLRP.Analysis.Polygon.Bridge
public import PercLib.CriticalLRP.Analysis.Polygon.Consumer
public import PercLib.CriticalLRP.Analysis.Polygon.UncutLink
public import PercLib.CriticalLRP.Analysis.Polygon.ChiInput
public import PercLib.CriticalLRP.Analysis.Polygon.NearBall
public import PercLib.CriticalLRP.Analysis.Polygon.TailConstant
public import PercLib.CriticalLRP.Analysis.Polygon.ConstantSharp
public import PercLib.CriticalLRP.Analysis.Polygon.Assembly
public import PercLib.CriticalLRP.Analysis.Polygon.ChiLower
public import PercLib.CriticalLRP.Analysis.Polygon.SmallRadius
public import PercLib.CriticalLRP.Analysis.Polygon.TailLog

namespace PercLib.CriticalLRP.I418C

-- generic layer
#print axioms polyK_one
#print axioms polyK_nonneg
#print axioms polyK_two
#print axioms polyK_three
#print axioms polyK_three_mono
#print axioms polyK_entry
#print axioms PowerInputs.chi_nonneg
#print axioms PowerInputs.ell_three_le
#print axioms split_bound
#print axioms rpow_card
#print axioms near_arith
#print axioms polygon_bound
#print axioms polygon_bound_sup
#print axioms polygon_bound_displayed
#print axioms one_le_polyK_three
-- non-vacuity witness
#print axioms witness_inputs
#print axioms witness_bound

end PercLib.CriticalLRP.I418C

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

-- model layer
#print axioms cutTwoPoint_eq_toReal
#print axioms cutKernel_le_uncut
#print axioms cutTwoPoint_le_twoPoint
#print axioms cutTwoPoint_self_eq_one
#print axioms cutTwoPoint_le_one
#print axioms cutTriPoint_def
#print axioms cutTriPoint_nonneg
#print axioms cutTriPoint_le_triSelf
#print axioms kernel_shift
#print axioms triPoint_le_self
#print axioms dist_zero_eq
#print axioms source_triSup
#print axioms source_triTail
#print axioms cutKpow_ne_top_of_chi_ne_top
#print axioms cutKpow_toReal_eq_polyK
#print axioms cutPolyK_comp_toReal
#print axioms source_powerInputs
#print axioms source_polyK_le_diag

end PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms PercLib.CriticalLRP.I418C.source_comp
#print axioms PercLib.CriticalLRP.I418C.source_polygon_bound
#print axioms PercLib.CriticalLRP.I418C.source_polygon_bound_of_cutoff_data

/- Axiom audit for the uncut-to-cutoff threefold comparison and its consumers. -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.Kpow_twoPointE_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPointE_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPoint_eq_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPointE_self
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPointE_comm
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.source_powerInputs_of_triSup
#print axioms PercLib.CriticalLRP.KernelPower.Kpow_mono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.Kpow_twoPointE_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.Kpow_twoPointE_three_eq_openTriangle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutTriPoint_le_triPoint
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.source_triSup'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.source_triTail'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.source_powerInputs'
#print axioms PercLib.CriticalLRP.I418C.source_polygon_bound'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.Kpow_two_le_three_self
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.Kpow_two_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_twoPoint_mul
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_twoPoint_conv_mul
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.polyK_twoPoint_eq_toReal_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hlink_derived
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hlink_betaCrit
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hB2_hB3_hlink_derived
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.source_ell_three_le
#print axioms PercLib.CriticalLRP.I418C.source_polygon_bound_of_cutoff_data'

/- Source tail and normalized balls. -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.nablaTail
#print axioms PercLib.CriticalLRP.I418C.NearBall.exists_cube_const
#print axioms PercLib.CriticalLRP.I418C.NearBall.card_le_of_cube_bound
#print axioms PercLib.CriticalLRP.I418C.NearBall.exists_card_const
#print axioms PercLib.CriticalLRP.I418C.NearBall.exists_small_ball_count
#print axioms PercLib.CriticalLRP.I418C.NearBall.exists_near_ball
#print axioms PercLib.CriticalLRP.I418C.NearBall.source_polygon_bound_sup_of_cutoff_data_uniform

/- The source triangle tail. -/
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.le_nablaTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.nablaTail_le_self
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.nablaTail_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.nablaTail_antitone
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.triPoint_le_nablaTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.nablaTail_toReal_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.nablaTail_toReal_le_triSelf
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.nablaTail_eq_openTriangleTail
#print axioms PercLib.CriticalLRP.I418C.source_polygon_bound_tail_cc
#print axioms PercLib.CriticalLRP.I418C.source_polygon_bound_tail_source_c
#print axioms PercLib.CriticalLRP.I418C.source_polygon_bound_of_cutoff_data_tail
#print axioms PercLib.CriticalLRP.I418C.source_polyK_three_le_triSelf

/- Cutoff first-moment conversion. -/
#print axioms PercLib.CriticalLRP.I418C.ChiInput.cutMassAt_ne_top_of_le_toReal
#print axioms PercLib.CriticalLRP.I418C.ChiInput.exists_lt_rpow_of_pos
#print axioms PercLib.CriticalLRP.I418C.ChiInput.exists_chi_lower_uniform_of_eventually
#print axioms PercLib.CriticalLRP.I418C.ChiInput.exists_chi_lower_uniform_of_tendsto_div
#print axioms PercLib.CriticalLRP.I418C.ChiInput.exists_chi_lower_uniform
#print axioms PercLib.CriticalLRP.I418C.ChiInput.exists_chi_lower_uniform_of_isEquivalent
#print axioms PercLib.CriticalLRP.I418C.ChiInput.exists_chi_lower_uniform_and_finite
#print axioms PercLib.CriticalLRP.I418C.ChiInput.source_polygon_bound_of_uniform_chi
#print axioms PercLib.CriticalLRP.I418C.ChiInput.exists_c0_source_polygon_bound
#print axioms PercLib.CriticalLRP.I418C.ChiInput.uncut_firstMoment_eq_top_of_chi_lower

/- Abstract sharpness witness. -/
#print axioms PercLib.CriticalLRP.I418C.Tconst
#print axioms PercLib.CriticalLRP.I418C.polyK_Tconst
#print axioms PercLib.CriticalLRP.I418C.powerInputs_Tconst
#print axioms PercLib.CriticalLRP.I418C.polygon_bound_Tconst_eq
#print axioms PercLib.CriticalLRP.I418C.polygon_bound_Tconst
#print axioms PercLib.CriticalLRP.I418C.no_smaller_constant
#print axioms PercLib.CriticalLRP.I418C.rpow_term_needed

#print axioms PercLib.CriticalLRP.I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment
#print axioms PercLib.CriticalLRP.I418C.ChiInput.betaCrit_pos_of_tendsto_chi_div

/- Conditional logarithmic-error behaviour of the polygon tail. -/
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_toReal_comp_rpow
#print axioms PercLib.CriticalLRP.Analysis.isLogErrorFunction_nablaTail_add_rpow_neg

/- Small and all-radius polygon estimates. -/
#print axioms PercLib.CriticalLRP.I418C.polygon_bound_small
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_cutMassAt_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.source_polygon_bound_small_of_finite
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.source_polygon_bound_small
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassAt_ne_top_of_le
#print axioms PercLib.CriticalLRP.I418C.NearBall.exists_small_near_ball
#print axioms PercLib.CriticalLRP.I418C.NearBall.exists_small_near_ball_of_near_ball
#print axioms PercLib.CriticalLRP.I418C.NearBall.not_forall_card_le_rpow
#print axioms PercLib.CriticalLRP.I418C.exists_uniform_source_polygon_bound_small_radius_of_finite
#print axioms PercLib.CriticalLRP.I418C.exists_uniform_source_polygon_bound_small_radius
#print axioms PercLib.CriticalLRP.I418C.exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii
#print axioms PercLib.CriticalLRP.I418C.source_polyK_three_le_small_radius

/- Lower comparison and the sign condition on the ODE error. -/
#print axioms PercLib.CriticalLRP.I418C.ChiLower.lower_of_ode_of_sign
#print axioms PercLib.CriticalLRP.I418C.ChiLower.eventually_lower_of_ode_of_tendsto_defect
#print axioms PercLib.CriticalLRP.I418C.ChiLower.eventually_lower_of_ode_of_E1_nonneg_of_tendsto_E0
#print axioms PercLib.CriticalLRP.I418C.ChiLower.sign_of_errors_mem_Icc
#print axioms PercLib.CriticalLRP.I418C.ChiLower.bounded_defect_insufficient
#print axioms PercLib.CriticalLRP.I418C.ChiLower.exists_normalizationError
#print axioms PercLib.CriticalLRP.I418C.ChiLower.cutMassAt_rpow_le_of_ode_of_sign
#print axioms PercLib.CriticalLRP.I418C.ChiLower.eventually_cutMassAt_rpow_le_of_E1_nonneg_of_tendsto_E0
#print axioms PercLib.CriticalLRP.I418C.ChiLower.exists_chi_lower_uniform_and_finite_of_E1_nonneg_of_tendsto_E0
#print axioms PercLib.CriticalLRP.I418C.ChiLower.eventually_cutMassAt_rpow_le_of_tendsto_defect
#print axioms PercLib.CriticalLRP.I418C.ChiLower.exists_chi_lower_uniform_and_finite_of_tendsto_defect
#print axioms PercLib.CriticalLRP.I418C.ChiLower.exists_c0_source_polygon_bound_of_ode
#print axioms PercLib.CriticalLRP.I418C.ChiLower.exists_c0_source_polygon_bound_of_E1_nonneg
#print axioms PercLib.CriticalLRP.I418C.ChiLower.exists_uniform_source_polygon_bound_of_ode
