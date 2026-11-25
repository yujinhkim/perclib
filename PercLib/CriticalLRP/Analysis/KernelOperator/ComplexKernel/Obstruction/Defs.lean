/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Definitions for the checked obstruction separating the Schur hypothesis from positivity.

Swarm `smwtxo95t`, member `m1`, direction (D) "concrete complex kernel operator".
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.Defs

/-!
# An indefinite symmetric nonnegative kernel

On the two-point lattice `Bool`, the off-diagonal kernel `κ x y = 1` for `x ≠ y` and `0` on the
diagonal is nonnegative, symmetric and has every row sum `1` — so it is a `SchurKernel` with
constant `1` — but its quadratic form at the vector `(1, -1)` equals `-2`.  Hence the Schur
hypothesis does not imply positivity of the real quadratic form: the hypothesis `hpos` of
`exists_sqrt_cube_kernelCLM` is genuine additional data.  Theorems in `Obstruction/Basic.lean`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.KernelOperator

/-- The off-diagonal kernel on two points: `1` off the diagonal, `0` on it. -/
def offDiagKernel : Bool → Bool → ℝ := fun x y => if x = y then 0 else 1

/-- The vector with values `1` and `-1` on the two points, as a real `ℓ²` function. -/
noncomputable def signLp : lp (fun _ : Bool => ℝ) 2 :=
  ⟨fun b => if b then 1 else -1, memℓp_gen (by exact Summable.of_finite)⟩

end PercLib.CriticalLRP.KernelOperator
