/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Cutoff two-point kernel in Schur coordinates

This is the actual range-truncated two-point function, represented as a
real two-variable kernel. Finiteness of its row sum is retained as a separate
premise; it is not inferred from `toReal` of an unconstrained critical mass.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.Model

@[expose] public section

namespace PercLib.CriticalLRP.KernelOperator

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- The two-point kernel of the range-truncated law as a two-variable real kernel. -/
noncomputable def cutKernel (r : ℝ) (x y : M.V) : ℝ := M.cutTwoPoint r x y

@[simp]
theorem cutKernel_apply (r : ℝ) (x y : M.V) : cutKernel M r x y = M.cutTwoPoint r x y := rfl


end

end PercLib.CriticalLRP.KernelOperator
