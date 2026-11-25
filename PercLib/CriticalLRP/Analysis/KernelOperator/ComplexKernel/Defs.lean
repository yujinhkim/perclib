/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Complex kernel operator: definitions.

Swarm `smwtxo95t`, member `m1`, direction (D) "concrete complex kernel operator".

The real operator `PercLib.CriticalLRP.KernelOperator.kernelCLM` acts on real `ℓ²` by the
lattice series `∑'_y κ x y * f y` (`Operator.lean`, `LpOperator.lean`).  The complex
continuous functional calculus, however, needs a complex Hilbert space.  This file introduces
the complex-linear kernel action; its summability, Schur bound, packaging as a bounded
`ℂ`-linear operator and agreement with the real operator are proved in `Basic.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.Defs

/-!
# The complex kernel action

`kernelApplyℂ κ f x = ∑'_y κ x y • f y` for `f : V → ℂ`.  No convergence is asserted by the
definition; `Basic.lean` supplies it from the Schur hypothesis.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*}

/-- The complex-linear action of the kernel `κ` on a complex-valued function,
`(kernelApplyℂ κ f) x = ∑'_y κ x y * f y`.  Convergence is not asserted here. -/
noncomputable def kernelApplyℂ (κ : V → V → ℝ) (f : V → ℂ) (x : V) : ℂ :=
  ∑' y, (κ x y : ℂ) * f y

end PercLib.CriticalLRP.KernelOperator

set_option linter.hashCommand false

/-! ### Axiom audit -/
#print axioms PercLib.CriticalLRP.KernelOperator.kernelApplyℂ
