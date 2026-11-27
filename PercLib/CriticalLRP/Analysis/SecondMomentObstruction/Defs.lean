/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# A monotone step-modulated power law

Integrated from accepted Ultramath `smwytmnfc`, member `m1`. This is an
obstruction witness for the ODE-to-regular-variation theorem, not a model of
critical percolation.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentRV

/-! # The obstruction function -/

@[expose] public section

namespace PercLib.CriticalLRP.ACSharpness

/-- The monotone step-modulated power law `r ↦ r ^ a * 2 ^ ⌊r⌋`. -/
noncomputable def stepPow (a : ℝ) (r : ℝ) : ℝ := r ^ a * (2 : ℝ) ^ (Nat.floor r)

end PercLib.CriticalLRP.ACSharpness
