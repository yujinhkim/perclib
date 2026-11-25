/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New deterministic proofs over PercLib's existing finite-certificate convention.
No upstream proof is copied; all configurations remain sets of coordinates.
-/
module

public import PercLib.Probability.DisjointOccurrence

/-! # Algebra of finite disjoint occurrence
Increasing events admit finite open witnesses. This yields associativity and
union distribution without countability or a probability law. The sure-event
identity for arbitrary events is restricted to finite coordinate types.
-/
@[expose] public section
open Set
namespace PercLib.Probability
variable {E : Type*}

/-- The impossible event cannot occur disjointly with any event. -/
theorem disjointOccurrence_empty_left (A : Set (Set E)) :
    disjointOccurrence ∅ A = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ω h
  exact (disjointOccurrence_subset_inter ∅ A h).1

theorem disjointOccurrence_empty_right (A : Set (Set E)) :
    disjointOccurrence A ∅ = ∅ := by
  rw [disjointOccurrence_comm, disjointOccurrence_empty_left]

/-- On a finite coordinate type every event has the entire configuration as a certificate. -/
theorem disjointOccurrence_univ_left [Finite E] (A : Set (Set E)) :
    disjointOccurrence Set.univ A = A := by
  apply Subset.antisymm
  · exact fun _ h => (disjointOccurrence_subset_inter _ _ h).2
  · intro ω hω
    refine ⟨∅, Set.univ, finite_empty, toFinite _, disjoint_bot_left, ?_, ?_⟩
    · intro _ _
      trivial
    · intro η hη
      have heq : η = ω := by ext e; exact hη e (mem_univ e)
      rwa [heq]

theorem disjointOccurrence_univ_right [Finite E] (A : Set (Set E)) :
    disjointOccurrence A Set.univ = A := by
  rw [disjointOccurrence_comm, disjointOccurrence_univ_left]

/-- Finite open certificates distribute through a union of increasing events. -/
theorem disjointOccurrence_union_left {A B C : Set (Set E)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hC : IsUpperSet C) :
    disjointOccurrence (A ∪ B) C = disjointOccurrence A C ∪ disjointOccurrence B C := by
  apply Subset.antisymm
  · intro ω hω
    obtain ⟨F, H, hF, hH, hd, hFω, hHω, hFab, hHC⟩ :=
      (mem_disjointOccurrence_iff_open (hA.union hB) hC ω).mp hω
    rcases hFab with hFA | hFB
    · exact Or.inl ((mem_disjointOccurrence_iff_open hA hC ω).mpr
        ⟨F, H, hF, hH, hd, hFω, hHω, hFA, hHC⟩)
    · exact Or.inr ((mem_disjointOccurrence_iff_open hB hC ω).mpr
        ⟨F, H, hF, hH, hd, hFω, hHω, hFB, hHC⟩)
  · rintro ω (h | h)
    · exact disjointOccurrence_mono subset_union_left Subset.rfl h
    · exact disjointOccurrence_mono subset_union_right Subset.rfl h

theorem disjointOccurrence_union_right {A B C : Set (Set E)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hC : IsUpperSet C) :
    disjointOccurrence A (B ∪ C) = disjointOccurrence A B ∪ disjointOccurrence A C := by
  rw [disjointOccurrence_comm A, disjointOccurrence_union_left hB hC hA,
    disjointOccurrence_comm B, disjointOccurrence_comm C]

/-- A nested disjoint occurrence of increasing events is exactly three pairwise
disjoint finite open certificates. No disjointness of vertices is substituted. -/
theorem mem_disjointOccurrence_three_iff {A B C : Set (Set E)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hC : IsUpperSet C) (ω : Set E) :
    ω ∈ disjointOccurrence (disjointOccurrence A B) C ↔
      ∃ F H K : Set E, F.Finite ∧ H.Finite ∧ K.Finite ∧
        Disjoint F H ∧ Disjoint F K ∧ Disjoint H K ∧
        F ⊆ ω ∧ H ⊆ ω ∧ K ⊆ ω ∧ F ∈ A ∧ H ∈ B ∧ K ∈ C := by
  constructor
  · intro hω
    obtain ⟨S, K, _, hK, hSK, hSω, hKω, hS, hKC⟩ :=
      (mem_disjointOccurrence_iff_open (isUpperSet_disjointOccurrence hA hB) hC ω).mp hω
    obtain ⟨F, H, hF, hH, hFH, hFS, hHS, hFA, hHB⟩ :=
      (mem_disjointOccurrence_iff_open hA hB S).mp hS
    exact ⟨F, H, K, hF, hH, hK, hFH, hSK.mono_left hFS, hSK.mono_left hHS,
      hFS.trans hSω, hHS.trans hSω, hKω, hFA, hHB, hKC⟩
  · rintro ⟨F, H, K, hF, hH, hK, hFH, hFK, hHK, hFω, hHω, hKω, hFA, hHB, hKC⟩
    apply (mem_disjointOccurrence_iff_open (isUpperSet_disjointOccurrence hA hB) hC ω).mpr
    refine ⟨F ∪ H, K, hF.union hH, hK, disjoint_union_left.mpr ⟨hFK, hHK⟩,
      union_subset hFω hHω, hKω, ?_, hKC⟩
    exact (mem_disjointOccurrence_iff_open hA hB (F ∪ H)).mpr
      ⟨F, H, hF, hH, hFH, subset_union_left, subset_union_right, hFA, hHB⟩

/-- Increasing-event disjoint occurrence is associative. -/
theorem disjointOccurrence_assoc {A B C : Set (Set E)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hC : IsUpperSet C) :
    disjointOccurrence (disjointOccurrence A B) C = disjointOccurrence A (disjointOccurrence B C) := by
  rw [disjointOccurrence_comm A (disjointOccurrence B C)]
  ext ω
  rw [mem_disjointOccurrence_three_iff hA hB hC,
    mem_disjointOccurrence_three_iff hB hC hA]
  constructor
  · rintro ⟨F, H, K, hF, hH, hK, hFH, hFK, hHK, hFω, hHω, hKω, hFA, hHB, hKC⟩
    exact ⟨H, K, F, hH, hK, hF, hHK, hFH.symm, hFK.symm, hHω, hKω, hFω, hHB, hKC, hFA⟩
  · rintro ⟨H, K, F, hH, hK, hF, hHK, hHF, hKF, hHω, hKω, hFω, hHB, hKC, hFA⟩
    exact ⟨F, H, K, hF, hH, hK, hHF.symm, hKF.symm, hHK, hFω, hHω, hKω, hFA, hHB, hKC⟩

/-- Three distinct open coordinates are witnessed by three disjoint singletons. -/
theorem disjointOccurrence_three_mem {i j k : E} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    disjointOccurrence (disjointOccurrence {ω | i ∈ ω} {ω | j ∈ ω}) {ω | k ∈ ω} =
      {ω | i ∈ ω ∧ j ∈ ω ∧ k ∈ ω} := by
  have hu (e : E) : IsUpperSet {ω : Set E | e ∈ ω} := fun _ _ h he => h he
  ext ω
  rw [mem_disjointOccurrence_three_iff (hu i) (hu j) (hu k)]
  constructor
  · rintro ⟨F, H, K, _, _, _, _, _, _, hFω, hHω, hKω, hi, hj, hk⟩
    exact ⟨hFω hi, hHω hj, hKω hk⟩
  · rintro ⟨hi, hj, hk⟩
    refine ⟨{i}, {j}, {k}, finite_singleton _, finite_singleton _, finite_singleton _,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

example : disjointOccurrence
    (disjointOccurrence {ω : Set (Fin 3) | 0 ∈ ω} {ω | 1 ∈ ω}) {ω | 2 ∈ ω} =
      {ω | 0 ∈ ω ∧ 1 ∈ ω ∧ 2 ∈ ω} :=
  disjointOccurrence_three_mem (by decide) (by decide) (by decide)

example (i : E) (C : Set (Set E)) :
    disjointOccurrence (disjointOccurrence {ω | i ∈ ω} {ω | i ∈ ω}) C = ∅ := by
  rw [disjointOccurrence_mem_self, disjointOccurrence_empty_left]

example (A : Set (Set Empty)) : disjointOccurrence Set.univ A = A :=
  disjointOccurrence_univ_left A

end PercLib.Probability
