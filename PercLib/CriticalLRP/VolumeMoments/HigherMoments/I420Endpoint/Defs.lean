/- Integration of independently rebuilt endpoint reflection work.
Production base a0162ec09fce17c3b392833e2ec0d965ac3a0a16.
Scratch source: repository-root .scratch/endpoint-reflection/.
-/

module

public import PercLib.CriticalLRP.Correlation.I417Example.Trans
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main

/-! Reflection and the pointwise mixed cluster-window expectation. -/
@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.I420Endpoint

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

variable {V : Type*} [Countable V] [AddCommGroup V]

/-- Reflection exchanging `x` and `y` in an abelian group: `z ↦ x + y - z`. -/
def reflect (x y : V) : V ≃ V where
  toFun z := x + y - z
  invFun z := x + y - z
  left_inv z := by dsimp; abel
  right_inv z := by dsimp; abel


/-- The pointwise mixed moment behind `I420Case1.mixedExcl`. -/
def mixedPoint (x y : V) (a b : ℕ) (ω : Config V) : ℝ≥0∞ :=
  clusterVol ω x ^ a *((cluster ω x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ b)


end PercLib.CriticalLRP.I420Endpoint
end
