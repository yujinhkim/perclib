/-
# Finiteness and packing of integer centres

A finite-volume outer set can contain only finitely many integer cells of volume
one. This gives the radius-indexed version of the counting sandwich.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Counting

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.LatticeGeometry

open MeasureTheory

open scoped ENNReal

variable {d : ℕ}

/-- A subadditive even rho whose outer radius has finite volume admits only
finitely many admissible integer centres. -/
theorem integer_centers_finite_of_volume_ne_top {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    {C r : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → ρ y ≤ C)
    (hfin : volume {x : Fin d → ℝ | ρ x ≤ r + C} ≠ ∞) :
    Set.Finite {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} := by
  by_contra h
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfin
  have hInf : {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r}.Infinite := h
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hInf N
  have hbound := card_le_volume_of_centers_le (d := d) (ρ := ρ) (C := C) (r := r)
    h_add h_neg hC s (fun z hz => hs hz)
  rw [hcard] at hbound
  exact lt_irrefl _ (hN.trans_le hbound)

/-- There is a finite admissible centre set whose cells realize the two-sided
radius counting sandwich, provided that the outer set has finite volume. -/
theorem exists_integer_centers_counting_sandwich {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    {C r : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → ρ y ≤ C)
    (hfin : volume {x : Fin d → ℝ | ρ x ≤ r + C} ≠ ∞) :
    ∃ s : Finset (Fin d → ℤ), (∀ z ∈ s, ρ (fun j => (z j : ℝ)) ≤ r) ∧
      volume {x : Fin d → ℝ | ρ x ≤ r - C} ≤ s.card ∧
      (s.card : ℝ≥0∞) ≤ volume {x : Fin d → ℝ | ρ x ≤ r + C} := by
  have hfinite := integer_centers_finite_of_volume_ne_top (d := d) (ρ := ρ)
    (C := C) (r := r) h_add h_neg hC hfin
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro z hz
    exact (Set.Finite.mem_toFinset hfinite).mp hz
  · apply counting_sandwich (d := d) (ρ := ρ) (C := C) (r := r) h_add h_neg hC hfinite.toFinset
    · intro z hz
      exact (Set.Finite.mem_toFinset hfinite).mp hz
    intro x hx
    have hx' := (integerCells_bounded_cubes (C := C) (r := r) ρ h_add h_neg hC).1 hx
    have h_eq : (⋃ (z : Fin d → ℤ) (_ : ρ (fun j => (z j : ℝ)) ≤ r), integerCell z) =
        ⋃ z ∈ hfinite.toFinset, integerCell z := by
      ext x
      simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact h_eq ▸ hx'

/-- The cardinalities of all admissible centres, rather than an unspecified
finite cover, satisfy the radius counting sandwich. -/
theorem ncard_integer_centers_sandwich {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    {C r : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → ρ y ≤ C)
    (hfin : volume {x : Fin d → ℝ | ρ x ≤ r + C} ≠ ∞) :
    volume {x : Fin d → ℝ | ρ x ≤ r - C} ≤
        (Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ≥0∞) ∧
      (Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ≥0∞) ≤
        volume {x : Fin d → ℝ | ρ x ≤ r + C} := by
  have hfinite := integer_centers_finite_of_volume_ne_top (d := d) (ρ := ρ)
    (C := C) (r := r) h_add h_neg hC hfin
  have hcover : {x : Fin d → ℝ | ρ x ≤ r - C} ⊆
      ⋃ z ∈ hfinite.toFinset, integerCell z := by
    intro x hx
    have hx' := (integerCells_bounded_cubes (C := C) (r := r) ρ h_add h_neg hC).1 hx
    simp only [Set.mem_iUnion] at hx' ⊢
    obtain ⟨z, hz, hxz⟩ := hx'
    exact ⟨z, (Set.Finite.mem_toFinset hfinite).mpr hz, hxz⟩
  have hs := counting_sandwich (d := d) (ρ := ρ) (C := C) (r := r)
    h_add h_neg hC hfinite.toFinset (fun z hz => (Set.Finite.mem_toFinset hfinite).mp hz)
    hcover
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hs

end PercLib.CriticalLRP.LatticeGeometry
