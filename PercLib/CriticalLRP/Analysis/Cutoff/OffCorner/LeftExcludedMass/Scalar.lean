/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.LeftExcludedMass.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerOneSided

/-!
# Strict scalar values and left derivatives at attained radii

The right derivative value of the cut mass uses its closed excluded-mass window.
Its left limit instead uses the strict window proved in `LeftExcludedMass.Main`.

The scalar coefficient β_c(-K') requires continuity of the kernel derivative only. If the
off-corner derivative family is supplied on a left window, the existing endpoint upgrade
gives the corresponding one-sided derivative of the cut mass at the endpoint.
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

/-- The scalar derivative value has the strict excluded-mass value as its left limit. -/
theorem tendsto_rhsScalarLt_nhdsLT {r0 r1 : ℝ} (hr0 : 0 < r0) (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤)
    (hK : ContinuousAt (fun r => deriv M.K r) r0) :
    Tendsto M.rhsScalar (𝓝[<] r0) (𝓝 (M.rhsScalarLt r0)) := by
  have hex := M.tendsto_exclScalar_nhdsLT_strict_of_le hr0 hr1 h2 h3
  have hcoeff : ContinuousAt M.coeffRHS r0 := hK.neg.const_mul ((M.betaCrit : ℝ))
  have hmul := (hcoeff.tendsto.mono_left nhdsWithin_le_nhds).mul hex
  change Tendsto (fun r => M.coeffRHS r * M.exclScalar r) (𝓝[<] r0)
    (𝓝 (M.coeffRHS r0 * M.exclScalarLt r0))
  exact hmul

/-- The strict left-corner derivative from an off-corner derivative family on a left window.
The finite second and third moments used to obtain the left scalar limit are at the larger
radius `r₁`. The family `F` is consumed verbatim; it is not replaced by the closed right value. -/
theorem hasDerivWithinAt_cutMassReal_Iic_strict_of_interval_deriv
    {a r0 r1 : ℝ} (ha : a < r0) (hr0 : 0 < r0) (hr1 : r0 < r1)
    (h2 : M.cutMoment 2 r1 ≠ ⊤) (h3 : M.cutMoment 3 r1 ≠ ⊤)
    (hK : ContinuousAt (fun r => deriv M.K r) r0)
    (hdiff : ∀ r ∈ Set.Ioo a r0, HasDerivAt M.cutMassReal (M.rhsScalar r) r) :
    HasDerivWithinAt M.cutMassReal (M.rhsScalarLt r0) (Set.Iic r0) r0 := by
  have hfin : M.cutMassAt r0 0 ≠ ⊤ := by
    rw [M.cutMassAt_zero_eq_cutMoment]
    exact M.cutMoment_one_ne_top_of_two (M.cutMoment_ne_top_of_le hr1.le 2 h2)
  exact M.hasDerivWithinAt_cutMassReal_Iic_of_interval_deriv M.rhsScalar ha hr0 hfin hdiff
    (M.tendsto_rhsScalarLt_nhdsLT hr0 hr1 h2 h3 hK)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_rhsScalarLt_nhdsLT
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivWithinAt_cutMassReal_Iic_strict_of_interval_deriv
