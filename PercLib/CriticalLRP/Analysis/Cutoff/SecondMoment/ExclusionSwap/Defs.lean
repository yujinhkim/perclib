/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Definitions for the excluded second-moment reflection

Integrated from accepted Ultramath `smwyrvajs`, member `m2`.  The reflection
at `y` exchanges `0` and `y`; its invariance properties for the radial cutoff
law and its excluded-moment consequences are proved in `ExclusionSwap.Main`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Defs

/-! # The midpoint reflection -/

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- The involution `x ↦ y - x` of `M.V = Fin M.d → ℤ`.  It maps `0` to `y` and `y` to `0`. -/
def reflEquiv (y : M.V) : M.V ≃ M.V where
  toFun x := y - x
  invFun x := y - x
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

end SourceModelData
end PercLib.CriticalLRP.Orchestration
