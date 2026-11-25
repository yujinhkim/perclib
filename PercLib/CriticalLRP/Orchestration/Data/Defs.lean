/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Supporting structures for the source-facing model definitions. All source constraints are kept
in the structure bodies. This is a genuine Lean definition layer, not a hypothesis expressing
any target theorem's conclusion.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry
public import PercLib.CriticalLRP.Analysis.RegularVariation
public import PercLib.CriticalLRP.KernelGeometry

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology Asymptotics

namespace PercLib.CriticalLRP.Orchestration

structure SourceNormData (d : ℕ) where
  ρ : (Fin d → ℝ) → ℝ
  ρ_zero : ρ 0 = 0
  ρ_pos : ∀ v : Fin d → ℝ, v ≠ 0 → 0 < ρ v
  ρ_neg : ∀ v : Fin d → ℝ, ρ (-v) = ρ v
  ρ_add_le : ∀ v w : Fin d → ℝ, ρ (v + w) ≤ ρ v + ρ w
  ρ_smul : ∀ (c : ℝ) (v : Fin d → ℝ), ρ (c • v) = |c| * ρ v
  ρ_continuous : Continuous ρ

  unitBall_volume : volume ({v : Fin d → ℝ | ρ v ≤ 1} : Set (Fin d → ℝ)) = 1



structure SourceModelData where
  d : ℕ
  hd : 1 ≤ d
  α : ℝ
  hα : 0 < α
  S : SourceNormData d

  K : ℝ → ℝ
  K_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ K r
  K_antitone : AntitoneOn K (Set.Ioi 0)
  K_diff : DifferentiableOn ℝ K (Set.Ioi 0)

  K_eq_integral : ∀ r : ℝ, 0 < r → K r = ∫ s in Ioi r, |deriv K s|


  exists_error : ∃ δ : ℝ → ℝ,
    (∀ r : ℝ, 0 < r → |deriv K r| = (1 + δ r) * r ^ (-(d : ℝ) - α - 1)) ∧
    Analysis.IsLogErrorFunction δ


end PercLib.CriticalLRP.Orchestration
