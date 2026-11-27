module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.StatisticsMeasurability

/-! # Tail integrability of the cutoff defect from finite second moments -/

@[expose] public section

noncomputable section

open MeasureTheory Measure Filter Set
open scoped ENNReal

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.CutoffDefect

open Orchestration
open PercLib.CriticalLRP.BallAverage
open PercLib.CriticalLRP.Analysis

/-- Finite second cutoff moments supply the a.e. measurability needed for the
existing tail logarithmic-integrability theorem. -/
theorem exists_integrableOn_cutE1_abs_div_of_secondMoment (M : SourceModelData)
    (hT : nablaSup M (openTriangleNabla M) 0 ≠ ⊤)
    (h1 : ∀ᶠ r : ℝ in atTop, M.cutMoment 1 r ≠ ⊤)
    {C p : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hF : LogRadialBound (fun x : M.V => M.S.ρ (toVec x))
      (openTriangleNabla M) C p)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤) :
    ∃ R : ℝ, 0 < R ∧ IntegrableOn (fun r => |cutE1 M r| / r) (Ioi R) :=
  integrableOn_cutE1_abs_div M hT h1 hC hp hF (aemeasurable_cutE1_of_secondMoment M h2)

#print axioms exists_integrableOn_cutE1_abs_div_of_secondMoment

end PercLib.CriticalLRP.CutoffDefect
