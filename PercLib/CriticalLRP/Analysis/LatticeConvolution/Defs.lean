/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Logarithmic and polynomial radial profiles for convolution bounds

Analytic profile definitions used for weighted layer-cake and shell-sum
arguments; these are not percolation two-point objects.
-/
module

public import Mathlib

namespace CriticalLRPConv

@[expose] public section

variable {G : Type*} [AddCommGroup G] {ρ : G → ℝ}

/-- `Λ x = log (2 + ρ x)`, the logarithmic profile of the source. -/
noncomputable def Lam (ρ : G → ℝ) (x : G) : ℝ := Real.log (2 + ρ x)

/-- `Λ` on the real line: `Λ(s) = log (2 + s)`. -/
noncomputable def LamR (s : ℝ) : ℝ := Real.log (2 + s)

/-- `w(r) = (1+r)^{-e} · (log (2+r))^{-c}`. -/
noncomputable def Wt (e c r : ℝ) : ℝ := (1 + r) ^ (-e) * LamR r ^ (-c)
