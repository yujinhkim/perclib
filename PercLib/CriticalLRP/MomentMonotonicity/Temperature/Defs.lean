/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Intensity-dependent cutoff mass

The definition and elementary comparison API for the cutoff first moment at
an arbitrary intensity. Parameter-left continuity and endpoint transfer are
proved in `MomentMonotonicity/Temperature.lean`.

Reviewed from Ultramath `smwtqkdul`, member `m8`, `BetaTransfer.lean`.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelMoments
public import PercLib.CriticalLRP.Analysis.Cutoff.Defs

/-! # Intensity-dependent cutoff mass and its elementary API -/

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP FiniteVolume CutoffMomentTransfer
open MeasureTheory
open scoped ENNReal NNReal

namespace SourceModelData

noncomputable section

variable (M : SourceModelData)

/-- `E_{β,r}|K_x|`: the cluster mass of `x` under the range-truncated law at
intensity `β`.  At `β = M.betaCrit` this is definitionally `M.cutMassAt r x`. -/
def cutMassAtBeta (β : ℝ≥0) (r : ℝ) (x : M.V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω x ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β)

@[simp]
theorem cutMassAtBeta_betaCrit (r : ℝ) (x : M.V) :
    M.cutMassAtBeta M.betaCrit r x = M.cutMassAt r x := rfl

/-- The range-truncated cluster mass is nondecreasing in the intensity. -/
theorem cutMassAtBeta_mono {β γ : ℝ≥0} (hβγ : β ≤ γ) (r : ℝ) (x : M.V) :
    M.cutMassAtBeta β r x ≤ M.cutMassAtBeta γ r x :=
  lintegral_clusterVol_mono
    (fun e => bernoulliEdgeProb_mono (M.cutKernel r) (M.cutKernel_nonneg r) hβγ e) x
end


end SourceModelData

end PercLib.CriticalLRP.Orchestration
