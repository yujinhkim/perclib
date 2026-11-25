/-
# Lebesgue volume of the integer lattice cells

This module computes volume one for every integer cell, the measure-theoretic
input for the tiling argument in Lemma I.4.6 of the supplied paper.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Basic

@[expose] public section

open scoped MeasureTheory

namespace PercLib.CriticalLRP.LatticeGeometry

variable {d : ℕ}

/-- Lebesgue measure of a half-open integer cell is one. -/
theorem volume_integerCell (z : Fin d → ℤ) : MeasureTheory.volume (integerCell z) = 1 := by
  rw [integerCell_eq_pi_Ico, Real.volume_pi_Ico]
  calc
    _ = ∏ _j : Fin d, (1 : ENNReal) := by
      apply Finset.prod_congr rfl (g := fun _ => (1 : ENNReal))
      intro j _
      rw [show ((z j : ℝ) + 1 - (z j : ℝ)) = (1 : ℝ) by ring]
      exact ENNReal.ofReal_one
    _ = 1 := Finset.prod_const_one

/-- Every integer cell is measurable. -/
theorem measurableSet_integerCell (z : Fin d → ℤ) : MeasurableSet (integerCell z) := by
  rw [integerCell_eq_pi_Ico]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ico

end PercLib.CriticalLRP.LatticeGeometry
