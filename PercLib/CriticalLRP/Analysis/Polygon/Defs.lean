/- Definitions shared by the I.4.18 polygon-analytic modules. Migrated from the
independently rebuilt submissions `smwqozn0q/m3` and existing cutoff modules.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Analysis.Cutoff.KpowSum
public import PercLib.CriticalLRP.Analysis.TriTail

@[expose] public section

noncomputable section

open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.I418C

variable {V : Type*} [Zero V] [DecidableEq V] [Countable V]

/-- An `n`-fold matrix power of a real kernel, written as an iterated sum. -/
noncomputable def polyK (T : V → V → ℝ) : ℕ → V → V → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | (n + 1) => fun x y => ∑' z, polyK T n x z * T z y

/-- Inputs to the analytic near/far polygon estimate, stated directly about real matrix powers.
`triSup` is deliberately an inequality: the cutoff threefold power is compared with the uncut
triangle, never identified with it. -/
structure PowerInputs (P : ℕ → V → V → ℝ) (nablaT χ : ℝ) : Prop where
  nonneg : ∀ (n : ℕ) (x y : V), 0 ≤ P n x y
  base : ∀ x y : V, P 0 x y = if x = y then 1 else 0
  comp : ∀ n : ℕ, P (n + 3) 0 0 = ∑' y, P 3 0 y * P n y 0
  compSummable : ∀ n : ℕ, Summable (fun y => P 3 0 y * P n y 0)
  colsum : ∀ n : ℕ, ∑' y, P n y 0 = χ ^ n
  colSummable : ∀ n : ℕ, Summable (fun y => P n y 0)
  entry : ∀ n : ℕ, 1 ≤ n → ∀ y : V, P n y 0 ≤ χ ^ (n - 1)
  selfOne : P 1 0 0 = 1
  triSup : ∀ y : V, P 3 0 y ≤ nablaT

/-- The constant-one kernel on the one-point space, used as a non-vacuity witness. -/
def T1 : PUnit → PUnit → ℝ := fun _ _ => 1

/-- The constant-one kernel on `Fin N`, used as an abstract sharpness witness for the polygon
estimate. This is not a percolation model on the infinite lattice. -/
def Tconst (N : ℕ) : Fin N → Fin N → ℝ := fun _ _ => 1

end PercLib.CriticalLRP.I418C

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I418C

variable (M : SourceModelData)

/-- The real open triangle at the uncut critical law. -/
noncomputable def triPoint (x y : M.V) : ℝ :=
  (PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit x y).toReal

/-- The uncut triangle diagram at the origin. -/
noncomputable def triSelf : ℝ := M.triPoint 0 0

/-- The open-triangle tail at the model's normalized source norm: `nablaTail M r` is
`sup_{y : ‖y‖ ≥ r} ∇_{β_c}(0,y)` in `ℝ≥0∞`, evaluated at the critical uncut law. -/
noncomputable def nablaTail (r : ℝ) : ℝ≥0∞ :=
  ⨆ y : M.V, ⨆ (_ : r ≤ M.S.dist 0 y),
    PercLib.CriticalLRP.TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y

/-- The cutoff threefold power: the factor that belongs in composition with cutoff powers. -/
noncomputable def cutTriPoint (r : ℝ) (y : M.V) : ℝ :=
  polyK (M.cutTwoPoint r) 3 0 y

end PercLib.CriticalLRP.Orchestration.SourceModelData
