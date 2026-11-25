/-
# Cube bounds for continuous functions, with an explicit l1 example

These results provide non-vacuity witnesses for integerCells_bounded_cubes.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Radius

@[expose] public section

open scoped BigOperators

namespace PercLib.CriticalLRP.LatticeGeometry

variable {d : ℕ}

private theorem abs_add_le_self (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rcases le_total 0 (a + b) with h | h
  · rw [abs_of_nonneg h]
    exact add_le_add (le_abs_self a) (le_abs_self b)
  · have ha : -a ≤ |a| := by simpa using le_abs_self (-a)
    have hb : -b ≤ |b| := by simpa using le_abs_self (-b)
    rw [abs_of_nonpos h]
    linarith

/-- Any continuous real-valued function is bounded above on the half-open
unit cube. A norm on the finite-dimensional space is a natural application. -/
theorem exists_unitCube_upper_bound (rho : (Fin d → ℝ) → ℝ) (hcont : Continuous rho) :
    ∃ C : ℝ, ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → rho y ≤ C := by
  have hcompact : IsCompact (Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun y hy => ?_⟩
  apply (le_abs_self (rho y)).trans
  apply hC
  intro j _
  exact ⟨(hy j).1, (hy j).2.le⟩

/-- The coordinate l1 norm is subadditive and even, with the dimension as a
uniform upper bound on the half-open unit cube. -/
theorem integerCells_bounded_cubes_l1 (r : ℝ) :
    {x : Fin d → ℝ | (∑ j, |x j|) ≤ r - (d : ℝ)} ⊆
      (⋃ (z : Fin d → ℤ) (_ : (∑ j, |(z j : ℝ)|) ≤ r), integerCell z) ∧
    (⋃ (z : Fin d → ℤ) (_ : (∑ j, |(z j : ℝ)|) ≤ r), integerCell z) ⊆
      {x : Fin d → ℝ | (∑ j, |x j|) ≤ r + (d : ℝ)} := by
  apply integerCells_bounded_cubes (rho := fun x => ∑ j, |x j|) (C := (d : ℝ))
  · intro x y
    calc
      (∑ j, |(x + y) j|) = ∑ j, |x j + y j| := by simp only [Pi.add_apply]
      _ ≤ ∑ j, (|x j| + |y j|) := by
        apply Finset.sum_le_sum
        intro j _
        exact abs_add_le_self (x j) (y j)
      _ = (∑ j, |x j|) + ∑ j, |y j| := Finset.sum_add_distrib
  · intro x
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.neg_apply, abs_neg]
  · intro y hy
    calc
      (∑ j, |y j|) ≤ ∑ _j : Fin d, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have hj := hy j
        rw [abs_of_nonneg hj.1]
        exact hj.2.le
      _ = (d : ℝ) := by simp

end PercLib.CriticalLRP.LatticeGeometry
