/-
# Integer lattice cells used by the tiling step of Lemma I.4.6

This file introduces the half-open unit cubes centred at integer points. It is
new formalization work for this branch. The mathematical source is the supplied
`attachments/i-want-you-to-ljpx/tom1.pdf`, Lemma I.4.6 on page 36.
-/
module

public import Mathlib

@[expose] public section

namespace PercLib.CriticalLRP.LatticeGeometry

variable {d : ℕ}

/-- The half-open unit cell centred at an integer point. -/
def integerCell (z : Fin d → ℤ) : Set (Fin d → ℝ) :=
  {x | ∀ j, (z j : ℝ) ≤ x j ∧ x j < (z j : ℝ) + 1}

/-- A cell is a product of half-open coordinate intervals. -/
theorem integerCell_eq_pi_Ico (z : Fin d → ℤ) :
    integerCell z = Set.univ.pi (fun j => Set.Ico (z j : ℝ) ((z j : ℝ) + 1)) := by
  ext x
  simp only [integerCell, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const,
    Set.mem_Ico]

/-- The set of points with rho-length at most `r`. -/
def rhoBall (ρ : (Fin d → ℝ) → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {x | ρ x ≤ r}

/-- Every real point belongs to an integer cell. -/
theorem exists_mem_integerCell (x : Fin d → ℝ) :
    ∃ z : Fin d → ℤ, x ∈ integerCell z := by
  refine ⟨fun j => Int.floor (x j), fun j => ?_⟩
  change (Int.floor (x j) : ℝ) ≤ x j ∧ x j < (Int.floor (x j) : ℝ) + 1
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- A point belongs to only one integer cell. -/
theorem integerCell_unique {z w : Fin d → ℤ}
    (h : (integerCell z ∩ integerCell w).Nonempty) : z = w := by
  obtain ⟨x, hxz, hxw⟩ := h
  funext j
  have hcast : ∀ a b : ℤ, ((a : ℝ) ≤ x j ∧ x j < (a : ℝ) + 1) →
      ((b : ℝ) ≤ x j ∧ x j < (b : ℝ) + 1) → a ≤ b := by
    intro a b ha hb
    by_contra hab
    have hba : b < a := lt_of_not_ge hab
    have hinc : (b : ℝ) + 1 ≤ (a : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hba)
    linarith [ha.2, hb.1]
  have h₁ : z j ≤ w j := by
    exact_mod_cast hcast (z j) (w j) (hxz j) (hxw j)
  have h₂ : w j ≤ z j := by
    exact_mod_cast hcast (w j) (z j) (hxw j) (hxz j)
  exact le_antisymm h₁ h₂

/-- Cells at distinct integer points are disjoint. -/
theorem integerCell_disjoint_of_ne {z w : Fin d → ℤ} (hzw : z ≠ w) :
    Disjoint (integerCell z) (integerCell w) := by
  apply Set.disjoint_left.mpr
  intro x hxz hxw
  exact hzw (integerCell_unique ⟨x, hxz, hxw⟩)

end PercLib.CriticalLRP.LatticeGeometry
