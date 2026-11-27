/- Integrated from `.scratch/case3-split-draft/DefectMeasurability.lean` at production base
`e48d8401fd028ac1ab1c9e40c6fb937a4c48b936`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffDefect.LogIntegrable

/-! # Measurability of the first-moment defect pieces -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

set_option linter.hashCommand false
set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- The standardization error is measurable: the standard derivative map is
Borel measurable, the normalized ball cardinality is measurable by monotonicity,
and the remaining formula is continuous in the radius. -/
theorem measurable_cutE0 (M : SourceModelData) : Measurable (PivotFlux.cutE0 M) := by
  have hJ : Measurable fun r => deriv M.K r := measurable_deriv _
  have hcard := CutoffDefect.measurable_ball_ncard M
  unfold PivotFlux.cutE0 VolumeMoments.oneSubE0
  fun_prop

/-- The composite ODE defect is measurable whenever both of its two factors are.
The remaining statistical input is thereby isolated to the `cutE1` factor, not
to `cutE0` or finite-real algebraic composition. -/
theorem measurable_cutError_of_measurables (M : SourceModelData)
    (hE0 : Measurable (PivotFlux.cutE0 M)) (hE1 : Measurable (PivotFlux.cutE1 M)) :
    Measurable (cutError M) := by
  unfold cutError
  fun_prop

/-- The defect itself, reduced to the exact three statistics used by
`CutoffDefect.measurable_cutE1_of_measurable_stats`. -/
theorem measurable_cutError_of_stats (M : SourceModelData)
    (hmass : Measurable fun r : ℝ => (M.cutMassAt r 0).toReal)
    (hpair : Measurable fun r : ℝ => (E1Sign.pairMass M r).toReal)
    (hconn : Measurable fun r : ℝ => (E1Sign.connMass M r).toReal) :
    Measurable (cutError M) :=
  measurable_cutError_of_measurables M (measurable_cutE0 M)
    (CutoffDefect.measurable_cutE1_of_measurable_stats M hmass hpair hconn)

#print axioms measurable_cutE0
#print axioms measurable_cutError_of_measurables
#print axioms measurable_cutError_of_stats

end I420Case3

end PercLib.CriticalLRP
