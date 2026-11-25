/-
# Radius bounds for the integer lattice-cell tessellation

These are the two inclusions in the proof of Lemma I.4.6, stated for a positive
cube-diameter bound. The leading constant in a general norm need not be estimated
for these inclusions. Only subadditivity and the uniform upper bound of rho on the
half-open unit cube are used.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Basic

@[expose] public section

namespace PercLib.CriticalLRP.LatticeGeometry

variable {d : ℕ}

/-- If a function is subadditive and bounded by `C` on the half-open unit cube,
the cells at radius at most `r` from the origin cover the radius `r-C` set and
are themselves covered by the radius `r+C` set. -/
theorem integerCells_bounded_cubes (rho : (Fin d → ℝ) → ℝ)
    (h_add : ∀ x y, rho (x + y) ≤ rho x + rho y)
    (h_neg : ∀ x, rho (-x) = rho x)
    {C r : ℝ}
    (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → rho y ≤ C) :
    {x : Fin d → ℝ | rho x ≤ r - C} ⊆
      (⋃ (z : Fin d → ℤ) (_ : rho (fun j => (z j : ℝ)) ≤ r), integerCell z) ∧
    (⋃ (z : Fin d → ℤ) (_ : rho (fun j => (z j : ℝ)) ≤ r), integerCell z) ⊆
      {x : Fin d → ℝ | rho x ≤ r + C} := by
  have hleft : {x | rho x ≤ r - C} ⊆
      (⋃ (z : Fin d → ℤ) (_ : rho (fun j => (z j : ℝ)) ≤ r), integerCell z) := by
    intro x hx
    let z : Fin d → ℤ := fun j => Int.floor (x j)
    have hfrac : ∀ j, 0 ≤ Int.fract (x j) ∧ Int.fract (x j) < 1 := by
      intro j
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hfracC : rho (fun j => Int.fract (x j)) ≤ C :=
      hC (fun j => Int.fract (x j)) hfrac
    have hcentre :
        rho (fun j => (z j : ℝ)) = rho (x - (fun j => Int.fract (x j))) := by
      congr 1
      funext j
      change (Int.floor (x j) : ℝ) = x j - Int.fract (x j)
      linarith [Int.self_sub_floor (x j)]
    have hbound : rho (fun j => (z j : ℝ)) ≤ r := by
      calc
        rho (fun j => (z j : ℝ)) = rho (x - (fun j => Int.fract (x j))) := hcentre
        _ ≤ rho x + rho (fun j => Int.fract (x j)) := by
          simpa only [sub_eq_add_neg, h_neg] using h_add x (-(fun j => Int.fract (x j)))
        _ ≤ (r - C) + C := add_le_add hx hfracC
        _ = r := by ring
    change x ∈ (⋃ (z : Fin d → ℤ) (_ : rho (fun j => (z j : ℝ)) ≤ r), integerCell z)
    rw [Set.mem_iUnion]
    refine ⟨z, Set.mem_iUnion.mpr ⟨hbound, ?_⟩⟩
    exact fun j => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  have hright : (⋃ (z : Fin d → ℤ) (_ : rho (fun j => (z j : ℝ)) ≤ r), integerCell z) ⊆
      {x | rho x ≤ r + C} := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨z, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨hz, hx⟩ := hx
    have hfrac : ∀ j, 0 ≤ x j - (z j : ℝ) ∧ x j - (z j : ℝ) < 1 := by
      intro j
      have hj := hx j
      constructor <;> linarith
    change rho x ≤ r + C
    calc
      rho x = rho ((fun j => (z j : ℝ)) + (x - (fun j => (z j : ℝ)))) := by congr 1; abel
      _ ≤ rho (fun j => (z j : ℝ)) + rho (x - (fun j => (z j : ℝ))) :=
        h_add (fun j => (z j : ℝ)) (x - (fun j => (z j : ℝ)))
      _ ≤ r + C := add_le_add hz (hC (x - (fun j => (z j : ℝ))) hfrac)
  exact ⟨hleft, hright⟩

end PercLib.CriticalLRP.LatticeGeometry
