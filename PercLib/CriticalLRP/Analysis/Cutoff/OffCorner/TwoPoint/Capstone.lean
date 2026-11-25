/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Capstone: continuity of the normalized pivotal mass off corner.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.PivotalFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.NormalizedAggregate.Main

/-!
# Continuity of the normalized pivotal mass off corner

Direction (C) of swarm `smwv2c2lw` (member `m3`, module `NormalizedAggregate.Main`) reduces
continuity of `M.normalizedPivotMass y` at an off-corner radius `r₀` to continuity of the
single-edge pivotal flux at the edges activated at `r₀`, together with a finite first cutoff
moment at one strictly larger radius.  The fixed-edge input is proved here
(`continuousAt_pivotalFlux_singleton`), so the composition is unconditional.

The remaining inputs are exactly the ones of the aggregate reduction: `r₀ > 0`, an off-corner
radius `r₀ ∉ M.attainedRadii`, and a finite first (or second) cutoff moment at one radius
`R > r₀`.  Nothing about the total normalized mass, the singleton flux sum or a two-point
function is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Continuity of the normalized pivotal mass off corner**, from a finite first cutoff
moment at one strictly larger radius. -/
theorem continuousAt_normalizedPivotMass {y : M.V} {r0 R : ℝ} (hr0 : 0 < r0) (hr0R : r0 < R)
    (hoff : r0 ∉ M.attainedRadii) (h1 : M.cutMoment 1 R ≠ ⊤) :
    ContinuousAt (M.normalizedPivotMass y) r0 :=
  M.continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux hr0 hr0R hoff h1
    fun e _ => M.continuousAt_pivotalFlux_singleton hr0 hr0R
      (by rw [M.cutMassAt_zero_eq_cutMoment]; exact h1) y e

/-- **Continuity of the normalized pivotal mass off corner**, from a finite second cutoff
moment at one strictly larger radius. -/
theorem continuousAt_normalizedPivotMass_of_moment_two {y : M.V} {r0 R : ℝ} (hr0 : 0 < r0)
    (hr0R : r0 < R) (hoff : r0 ∉ M.attainedRadii) (h2 : M.cutMoment 2 R ≠ ⊤) :
    ContinuousAt (M.normalizedPivotMass y) r0 :=
  M.continuousAt_normalizedPivotMass_of_continuousAt_pivotalFlux_of_moment_two hr0 hr0R hoff h2
    fun e _ => M.continuousAt_pivotalFlux_singleton_of_cutMoment hr0 hr0R h2 y e

end SourceModelData

end PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.continuousAt_normalizedPivotMass
#print axioms SourceModelData.continuousAt_normalizedPivotMass_of_moment_two
