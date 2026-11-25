/-
# Finite-cell volume and the counting sandwich

Mathematical source: the proof of Lemma I.4.6 in the supplied paper. The
counting formulation was independently checked against the member submission
`.ultramath/smwiyjuem/m1/PercLib/CriticalLRP/LatticeGeometry/Counting.lean`
and adapted to the existing `integerCell` and radius interfaces.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Radius
public import PercLib.CriticalLRP.LatticeGeometry.Cell.Volume
public import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.LatticeGeometry

open MeasureTheory

open scoped ENNReal

variable {d : ℕ}

/-- A finite union of distinct integer cells has volume equal to its cardinality. -/
theorem volume_biUnion_integerCell (s : Finset (Fin d → ℤ)) :
    volume (⋃ z ∈ s, integerCell z) = s.card := by
  rw [measure_biUnion_finset (f := integerCell) (s := s)
    (fun z _ w _ hzw => integerCell_disjoint_of_ne hzw)
    (fun z _ => measurableSet_integerCell z)]
  simp [volume_integerCell]

/-- Any set containing the cells of a finite set of centres has measure at
least its cardinality. -/
theorem card_le_volume_of_biUnion_integerCell_subset (s : Finset (Fin d → ℤ))
    {T : Set (Fin d → ℝ)} (hT : (⋃ z ∈ s, integerCell z) ⊆ T) :
    (s.card : ℝ≥0∞) ≤ volume T := by
  rw [← volume_biUnion_integerCell s]
  exact measure_mono hT

/-- A set contained in the cells of a finite set of centres has measure at most
its cardinality. -/
theorem volume_le_card_of_subset_biUnion_integerCell (s : Finset (Fin d → ℤ))
    {T : Set (Fin d → ℝ)} (hT : T ⊆ ⋃ z ∈ s, integerCell z) :
    volume T ≤ s.card := by
  rw [← volume_biUnion_integerCell s]
  exact measure_mono hT

/-- Admissible centres give a lower bound for the measure of the outer set. -/
theorem card_le_volume_of_centers_le {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    {C r : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → ρ y ≤ C)
    (s : Finset (Fin d → ℤ)) (hs : ∀ z ∈ s, ρ (fun j => (z j : ℝ)) ≤ r) :
    (s.card : ℝ≥0∞) ≤ volume {x : Fin d → ℝ | ρ x ≤ r + C} := by
  refine card_le_volume_of_biUnion_integerCell_subset s ?_
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨z, hz, hmem⟩ := hx
  exact (integerCells_bounded_cubes (C := C) (r := r) ρ h_add h_neg hC).2
    (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hs z hz, hmem⟩⟩)

/-- **The counting sandwich.** For a finite set of admissible centres covering
the inner set, its cardinality is between the inner and outer measures. -/
theorem counting_sandwich {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    {C r : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → ρ y ≤ C)
    (s : Finset (Fin d → ℤ)) (hs : ∀ z ∈ s, ρ (fun j => (z j : ℝ)) ≤ r)
    (hcover : {x : Fin d → ℝ | ρ x ≤ r - C} ⊆ ⋃ z ∈ s, integerCell z) :
    volume {x : Fin d → ℝ | ρ x ≤ r - C} ≤ s.card ∧
      (s.card : ℝ≥0∞) ≤ volume {x : Fin d → ℝ | ρ x ≤ r + C} :=
  ⟨volume_le_card_of_subset_biUnion_integerCell s hcover,
    card_le_volume_of_centers_le h_add h_neg hC s hs⟩

end PercLib.CriticalLRP.LatticeGeometry
