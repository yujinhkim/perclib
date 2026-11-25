/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.LeftExcludedMass.Scalar
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RightExcludedMass.Corner
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RightExcludedMass.Positive

/-!
# Assembling the two one-sided cutoff derivatives at an attained radius

The left strict-window mass is defined using the mark representation, while the right
strict-window mass is defined directly under the cutoff law.  This module proves their equality
by mapping the marks to a configuration; consequently the two strict scalar values are the same.

With this identification, the proved left derivative in `LeftExcludedMass.Scalar` and the proved
right derivative in `RightExcludedMass.Main` have different values whenever the activation shell
has positive mass and the scalar coefficient is positive.  Two-sided differentiability is then
impossible.  The attained-radius version gets shell positivity from
`RightExcludedMass.Positive`; it does not assert differentiability or exclude any attained radius.
All off-corner derivative families and moment hypotheses remain explicit inputs.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- Mapping the mark representation identifies the left and right strict-window masses. -/
theorem exclMassLt_eq_exclMassStrict (r : ℝ) :
    M.exclMassLt r = M.exclMassStrict r := by
  rw [SourceModelData.exclMassLt, SourceModelData.exclMassStrict,
    E1Sign.cutLaw_eq, ← markMeasure_map_atParameter]
  symm
  rw [lintegral_map (M.measurable_exclMassStrictFun r) (measurable_atParameter _)]
  apply lintegral_congr
  intro u
  rw [SourceModelData.exclMarkFunLt, SourceModelData.markVol]

/-- The two real strict-window masses agree. -/
theorem exclScalarLt_eq_exclScalarStrict (r : ℝ) :
    M.exclScalarLt r = M.exclScalarStrict r := by
  rw [SourceModelData.exclScalarLt, SourceModelData.exclScalarStrict,
    M.exclMassLt_eq_exclMassStrict r]

/-- The left derivative value is the coefficient times the right module's strict-window mass. -/
theorem rhsScalarLt_eq_coeffRHS_mul_exclScalarStrict (r : ℝ) :
    M.rhsScalarLt r = M.coeffRHS r * M.exclScalarStrict r := by
  rw [SourceModelData.rhsScalarLt, M.exclScalarLt_eq_exclScalarStrict r]

/-- An attained radius has a nonempty activation shell. -/
theorem shellF_nonempty_of_mem_attainedRadii {r : ℝ}
    (hratt : r ∈ M.attainedRadii) : (M.shellF r).Nonempty := by
  obtain ⟨x, hx0, hxr⟩ := M.mem_attainedRadii.mp hratt
  refine ⟨x, M.mem_shellF.mpr ?_⟩
  rw [← SourceNormData.dist_zero_right, hxr]

/-- The shell mass is nonzero at every attained radius; attained radii are positive. -/
theorem exclMassShell_ne_zero_of_attained {r : ℝ}
    (hratt : r ∈ M.attainedRadii) : M.exclMassShell r ≠ 0 :=
  M.exclMassShell_ne_zero_of_shell (M.attainedRadii_pos hratt)
    (M.shellF_nonempty_of_mem_attainedRadii hratt)

/-- The positivity theorem is non-vacuous: every normalized source model has such a radius. -/
theorem exists_exclMassShell_ne_zero :
    ∃ r : ℝ, 0 < r ∧ M.exclMassShell r ≠ 0 := by
  obtain ⟨r, hratt⟩ := M.S.attainedRadii_nonempty M.hd
  exact ⟨r, M.attainedRadii_pos hratt, M.exclMassShell_ne_zero_of_attained hratt⟩

/-- Off-corner derivative families on both sides give an exact left/right derivative at the corner.
If the strict shell mass is nonzero and the coefficient is positive, these values differ. -/
theorem not_hasDerivAt_of_two_sided_interval_deriv_of_shell {a r0 r1 : ℝ}
    (ha : a < r0) (hr0 : 0 < r0) (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤)
    (hK : ContinuousAt (fun r => deriv M.K r) r0)
    (hdiffLeft : ∀ r ∈ Set.Ioo a r0, HasDerivAt M.cutMassReal (M.rhsScalar r) r)
    (hdiffRight : ∀ r ∈ Set.Ioo r0 r1, HasDerivAt M.cutMassReal (M.rhsScalar r) r)
    (hshell : M.exclMassShell r0 ≠ 0) (hcoeffpos : 0 < M.coeffRHS r0) :
    ¬ ∃ L, HasDerivAt M.cutMassReal L r0 := by
  have h2r0 : M.cutMoment 2 r0 ≠ ⊤ := M.cutMoment_ne_top_of_le hr1.le 2 h2
  have hfin : M.cutMassAt r1 0 ≠ ⊤ :=
    ne_top_of_le_ne_top h2 (E1Sign.cutMassAt_le_cutMoment_two M r1)
  have hleft := M.hasDerivWithinAt_cutMassReal_Iic_strict_of_interval_deriv
    ha hr0 hr1 h2 h3 hK hdiffLeft
  have hbound : M.rhsScalarLt r0 ≤ M.coeffRHS r0 * M.exclScalarStrict r0 :=
    le_of_eq (M.rhsScalarLt_eq_coeffRHS_mul_exclScalarStrict r0)
  exact M.not_hasDerivAt_of_left_le_strictScalar_of_shell hr0 hr1 h2 h3 h2r0 hK
    hdiffRight hfin hleft hbound hshell hcoeffpos

/-- At an attained positive radius with positive scalar coefficient, compatible off-corner
 derivative families on both sides imply that the cutoff mass is not two-sided differentiable. -/
theorem not_hasDerivAt_of_two_sided_interval_deriv_of_attained {a r0 r1 : ℝ}
    (ha : a < r0) (hr0 : 0 < r0) (hr1 : r0 < r1)
    (hratt : r0 ∈ M.attainedRadii)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤)
    (hK : ContinuousAt (fun r => deriv M.K r) r0)
    (hdiffLeft : ∀ r ∈ Set.Ioo a r0, HasDerivAt M.cutMassReal (M.rhsScalar r) r)
    (hdiffRight : ∀ r ∈ Set.Ioo r0 r1, HasDerivAt M.cutMassReal (M.rhsScalar r) r)
    (hcoeffpos : 0 < M.coeffRHS r0) :
    ¬ ∃ L, HasDerivAt M.cutMassReal L r0 :=
  M.not_hasDerivAt_of_two_sided_interval_deriv_of_shell ha hr0 hr1 h2 h3 hK
    hdiffLeft hdiffRight (M.exclMassShell_ne_zero_of_attained hratt) hcoeffpos

end SourceModelData
end PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassLt_eq_exclMassStrict
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclScalarLt_eq_exclScalarStrict
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.rhsScalarLt_eq_coeffRHS_mul_exclScalarStrict
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.shellF_nonempty_of_mem_attainedRadii
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassShell_ne_zero_of_attained
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_exclMassShell_ne_zero
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.not_hasDerivAt_of_two_sided_interval_deriv_of_shell
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.not_hasDerivAt_of_two_sided_interval_deriv_of_attained
