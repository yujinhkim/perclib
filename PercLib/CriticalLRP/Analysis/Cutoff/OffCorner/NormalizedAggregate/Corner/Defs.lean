/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.KernelFactor.Main

/-!
# Left-continuous normalized pivotal factors

The left/strict cutoff factor excludes all edges whose length equals the current radius.
It is used to describe the normalized pivotal mass at an attained radius, where that
shell is activated only from the right.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The normalized pivotal factor seen from the left of `r`: a non-loop edge of length `s`
is counted only for `s < r`, with the same `exp (-β_c K s)` normalization as for `s ≤ r`. -/
noncomputable def cutPivotFactorLT (r : ℝ) : Sym2 M.V → ℝ :=
  radialSym M.S (fun s => if s < r then Real.exp (-((M.betaCrit : ℝ) * M.K s)) else 0)

end SourceModelData

end PercLib.CriticalLRP.Orchestration
