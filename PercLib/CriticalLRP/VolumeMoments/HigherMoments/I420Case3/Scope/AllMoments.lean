module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Measurability
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.AllMoments
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.StatisticsMeasurability

/-! # Finite-first-moment consequences for the Case-3 scope -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.I420Case3

open Orchestration

/-- The full ODE defect is a.e. measurable on the tail of finite second cutoff moments. -/
theorem aemeasurable_cutError_of_secondMoment (M : SourceModelData)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    AEMeasurable (cutError M) (volume.restrict (Set.Ioi 1)) := by
  have hE0 : AEMeasurable (fun r => (1 : ℝ) - PivotFlux.cutE0 M r)
      (volume.restrict (Set.Ioi 1)) :=
    aemeasurable_const.sub (measurable_cutE0 M).aemeasurable
  have hE1 : AEMeasurable (fun r => (1 : ℝ) - PivotFlux.cutE1 M r)
      (volume.restrict (Set.Ioi 1)) :=
    aemeasurable_const.sub (CutoffDefect.aemeasurable_cutE1_of_secondMoment M h2)
  exact aemeasurable_const.sub (hE0.mul hE1)

/-- At an arbitrary normalized norm, a finite first cutoff moment supplies
finite second moments and hence tail measurability of the complete ODE defect. -/
theorem aemeasurable_cutError_of_firstMoment (M : SourceModelData)
    (h1 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) :
    AEMeasurable (cutError M) (volume.restrict (Set.Ioi 1)) :=
  aemeasurable_cutError_of_secondMoment M fun r hr =>
    Orchestration.cutMoment_ne_top_of_one M r (h1 r hr) 2

#print axioms aemeasurable_cutError_of_secondMoment
#print axioms aemeasurable_cutError_of_firstMoment

end PercLib.CriticalLRP.I420Case3
