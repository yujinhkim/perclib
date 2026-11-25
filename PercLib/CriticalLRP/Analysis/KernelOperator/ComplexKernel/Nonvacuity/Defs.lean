/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Definitions for the non-vacuity witness of the complex kernel operator package.

Swarm `smwtxo95t`, member `m1`, direction (D) "concrete complex kernel operator".
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.Defs

/-!
# A one-point lattice witness

The constant-one kernel on `Unit` and the constant-one real `ℓ²` function on `Unit`; the
theorems about them are in `Nonvacuity/Basic.lean`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.KernelOperator

/-- The constant-one kernel on the one-point lattice. -/
def oneKernel : Unit → Unit → ℝ := fun _ _ => 1

/-- The constant-one real `ℓ²` function on the one-point lattice. -/
noncomputable def oneLp : lp (fun _ : Unit => ℝ) 2 :=
  ⟨fun _ => 1, memℓp_gen (by exact Summable.of_finite)⟩

end PercLib.CriticalLRP.KernelOperator

set_option linter.hashCommand false

/-! ### Axiom audit (definitions) -/
#print axioms PercLib.CriticalLRP.KernelOperator.oneKernel
#print axioms PercLib.CriticalLRP.KernelOperator.oneLp
