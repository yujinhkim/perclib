/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from NearCritical/DisjointOccurrence.lean and the certificate part of
NearCritical/BK.lean at tomhutchcroft/near-critical-diffusivity,
revision c820fea91a7482c1755de0ec94ecb9f59ccfcacc, with Tom Hutchcroft's reuse
permission recorded in docs/DECISIONS.md R-3. The upstream native files have no
per-file licence header; this notice records permission rather than attributing
an Apache licence to them. No vendored third-party file is copied here.

Changed on 2026-11-14: configurations are sets, increasingness is mathlib's
IsUpperSet, and unrelated harmonic-network dependencies are omitted.
-/
module

public import PercLib.Probability.ProdBernoulli
public import Mathlib.Order.UpperLower.Basic

/-!
# Finite forcing certificates and disjoint occurrence

Certificates specify finitely many coordinates, including closed coordinates.
They force the event for every assignment outside the certificate. Disjointness
is disjointness of coordinates, so bond applications use edges, not vertices.
For increasing events, certificates can be replaced by disjoint finite open sets.
-/

@[expose] public section

namespace PercLib.Probability

variable {ι : Type*}

/-- Fixing the coordinates in `F` to their values in `ω` forces `A`, regardless
of all coordinates outside `F`. No finiteness is part of this auxiliary predicate. -/
def ForcesOn (A : Set (Set ι)) (ω F : Set ι) : Prop :=
  ∀ η : Set ι, (∀ i ∈ F, i ∈ η ↔ i ∈ ω) → η ∈ A

/-- Disjoint occurrence with two disjoint finite universal forcing certificates. -/
def disjointOccurrence (A B : Set (Set ι)) : Set (Set ι) :=
  {ω | ∃ F H : Set ι, F.Finite ∧ H.Finite ∧ Disjoint F H ∧
    ForcesOn A ω F ∧ ForcesOn B ω H}

theorem ForcesOn.mem {A : Set (Set ι)} {ω F : Set ι} (h : ForcesOn A ω F) : ω ∈ A :=
  h ω (fun _ _ => Iff.rfl)

/-- Both events occur whenever they occur disjointly. -/
theorem disjointOccurrence_subset_inter (A B : Set (Set ι)) :
    disjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨F, H, _, _, _, hF, hH⟩
  exact ⟨hF.mem, hH.mem⟩

theorem disjointOccurrence_comm (A B : Set (Set ι)) :
    disjointOccurrence A B = disjointOccurrence B A := by
  ext ω
  constructor <;> rintro ⟨F, H, hF, hH, hd, hA, hB⟩
  · exact ⟨H, F, hH, hF, hd.symm, hB, hA⟩
  · exact ⟨H, F, hH, hF, hd.symm, hB, hA⟩

theorem disjointOccurrence_mono {A B C D : Set (Set ι)}
    (hAC : A ⊆ C) (hBD : B ⊆ D) : disjointOccurrence A B ⊆ disjointOccurrence C D := by
  rintro ω ⟨F, H, hF, hH, hd, hA, hB⟩
  exact ⟨F, H, hF, hH, hd, fun η he => hAC (hA η he), fun η he => hBD (hB η he)⟩

/-- The smallest configuration agreeing with `ω` on `F` is `F ∩ ω`. -/
theorem ForcesOn.inter_mem {A : Set (Set ι)} {ω F : Set ι} (h : ForcesOn A ω F) :
    F ∩ ω ∈ A :=
  h (F ∩ ω) (fun _ hi => by simp [hi])

/-- For increasing events, finite open certificates give exactly the same event. -/
theorem mem_disjointOccurrence_iff_open {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (ω : Set ι) :
    ω ∈ disjointOccurrence A B ↔
      ∃ F H : Set ι, F.Finite ∧ H.Finite ∧ Disjoint F H ∧
        F ⊆ ω ∧ H ⊆ ω ∧ F ∈ A ∧ H ∈ B := by
  constructor
  · rintro ⟨F, H, hF, hH, hd, hf, hh⟩
    exact ⟨F ∩ ω, H ∩ ω, hF.subset Set.inter_subset_left,
      hH.subset Set.inter_subset_left, hd.mono Set.inter_subset_left Set.inter_subset_left,
      Set.inter_subset_right, Set.inter_subset_right, hf.inter_mem, hh.inter_mem⟩
  · rintro ⟨F, H, hF, hH, hd, hFω, hHω, hf, hh⟩
    refine ⟨F, H, hF, hH, hd, ?_, ?_⟩
    · intro η he
      exact hA (fun i hi => (he i hi).mpr (hFω hi)) hf
    · intro η he
      exact hB (fun i hi => (he i hi).mpr (hHω hi)) hh

theorem isUpperSet_disjointOccurrence {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) : IsUpperSet (disjointOccurrence A B) := by
  intro ω η hωη hω
  obtain ⟨F, H, hF, hH, hd, hf, hh, hFA, hHB⟩ :=
    (mem_disjointOccurrence_iff_open hA hB ω).mp hω
  exact (mem_disjointOccurrence_iff_open hA hB η).mpr
    ⟨F, H, hF, hH, hd, hf.trans hωη, hh.trans hωη, hFA, hHB⟩

/-- An indispensable open coordinate cannot serve as two disjoint witnesses. -/
theorem disjointOccurrence_mem_self (i : ι) :
    disjointOccurrence {ω | i ∈ ω} {ω | i ∈ ω} = ∅ := by
  have hu : IsUpperSet {ω : Set ι | i ∈ ω} := fun _ _ h hi => h hi
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω h
  obtain ⟨F, H, _, _, hd, _, _, hiF, hiH⟩ :=
    (mem_disjointOccurrence_iff_open hu hu ω).mp h
  exact Set.disjoint_left.mp hd hiF hiH

/-- Distinct open coordinates have disjoint singleton certificates. -/
theorem disjointOccurrence_mem_mem {i j : ι} (hij : i ≠ j) :
    disjointOccurrence {ω | i ∈ ω} {ω | j ∈ ω} = {ω | i ∈ ω ∧ j ∈ ω} := by
  apply Set.Subset.antisymm (disjointOccurrence_subset_inter _ _)
  rintro ω ⟨hi, hj⟩
  refine ⟨{i}, {j}, Set.finite_singleton _, Set.finite_singleton _, ?_, ?_, ?_⟩
  · simpa using hij
  · intro η he
    exact (he i (Set.mem_singleton i)).mpr hi
  · intro η he
    exact (he j (Set.mem_singleton j)).mpr hj

/-- The empty certificates force the sure event, even on an empty index type. -/
theorem disjointOccurrence_univ :
    disjointOccurrence (Set.univ : Set (Set ι)) Set.univ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  exact ⟨∅, ∅, Set.finite_empty, Set.finite_empty, disjoint_bot_left,
    fun _ _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩

example : disjointOccurrence (Set.univ : Set (Set Empty)) Set.univ = Set.univ :=
  disjointOccurrence_univ

example : disjointOccurrence {ω : Set Bool | false ∈ ω} {ω | true ∈ ω} =
    {ω | false ∈ ω ∧ true ∈ ω} :=
  disjointOccurrence_mem_mem Bool.false_ne_true

end PercLib.Probability
