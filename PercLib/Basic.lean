module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

@[expose] public section

namespace PercLib

/-- A small initial theorem exercising mathlib and nonlinear arithmetic. -/
theorem two_mul_le_add_sq (a b : ℝ) :
    2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

end PercLib
