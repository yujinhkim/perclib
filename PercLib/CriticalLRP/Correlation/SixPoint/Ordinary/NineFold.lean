/-
Nine-singleton BK: pairwise disjoint finite open certificates for a `Fin k`-indexed family of
increasing events force the iterated disjoint occurrence, and the latter has probability at most
the product of the probabilities (`countable_profile_bk`, iterated).

This is the `k = 0` event-side machinery: the nine walks of the split six-terminal arm system
(`Attachment.Split.combSystem_nine`) enter as nine pairwise disjoint finite certificates, with no
joint pair and no second-moment factor.

Supplied by Ultramath `smwpv4yqm` member `m1` (direction d3, task direction A).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.Defs

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Probability
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

/-! ## Monotonicity -/

theorem isUpperSet_iterDC {ι : Type*} :
    ∀ (k : ℕ) (A : Fin k → Set (Set ι)), (∀ i, IsUpperSet (A i)) → IsUpperSet (iterDC k A)
  | 0, _, _ => isUpperSet_univ
  | (k + 1), A, hA =>
      isUpperSet_disjointOccurrence
        (isUpperSet_iterDC k (fun i => A i.castSucc) fun _ => hA _) (hA _)

/-! ## Reindexing a union over `Fin (k+1)` -/

theorem iUnion_fin_succ {α : Type*} {k : ℕ} (W : Fin (k + 1) → Set α) :
    (⋃ i, W i) = (⋃ i : Fin k, W i.castSucc) ∪ W (Fin.last k) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | h
    · exact Or.inl ⟨j, hi⟩
    · exact Or.inr (h ▸ hi)
  · rintro (⟨j, hj⟩ | h)
    · exact ⟨j.castSucc, hj⟩
    · exact ⟨_, h⟩

/-! ## Certificates imply the iterated disjoint occurrence -/

/-- **Pairwise disjoint finite certificates imply the iterated disjoint occurrence.**  If
`W i ∈ A i` and the `W i` are pairwise disjoint and finite, then their union lies in
`iterDC k A`.  No measurability is used, only `IsUpperSet` of the events. -/
theorem iUnion_mem_iterDC_of_witnesses {ι : Type*} :
    ∀ (k : ℕ) (A : Fin k → Set (Set ι)), (∀ i, IsUpperSet (A i)) →
      ∀ W : Fin k → Set ι, (∀ i, (W i).Finite) → (∀ i, W i ∈ A i) →
        Pairwise (fun i j => Disjoint (W i) (W j)) → (⋃ i, W i) ∈ iterDC k A
  | 0, _, _, _, _, _, _ => by simp [iterDC]
  | (k + 1), A, hA, W, hWfin, hWmem, hWdisj => by
    have hrec : (⋃ i : Fin k, W i.castSucc) ∈ iterDC k (fun i => A i.castSucc) :=
      iUnion_mem_iterDC_of_witnesses k (fun i => A i.castSucc) (fun i => hA _)
        (fun i => W i.castSucc) (fun i => hWfin _) (fun i => hWmem _)
        (fun i j hij => hWdisj (i := i.castSucc) (j := j.castSucc)
          (fun h => hij (Fin.castSucc_inj.mp h)))
    have hfin : (⋃ i : Fin k, W i.castSucc).Finite :=
      Set.finite_iUnion fun i => hWfin _
    have hdisj : Disjoint (⋃ i : Fin k, W i.castSucc) (W (Fin.last k)) := by
      rw [Set.disjoint_iUnion_left]
      exact fun i => hWdisj (i := i.castSucc) (j := Fin.last k) (Fin.castSucc_ne_last i)
    have hmem : (⋃ i : Fin k, W i.castSucc) ∪ W (Fin.last k) ∈
        disjointOccurrence (iterDC k (fun i => A i.castSucc)) (A (Fin.last k)) :=
      (mem_disjointOccurrence_iff_open (isUpperSet_iterDC k (fun i => A i.castSucc)
        fun _ => hA _) (hA _) _).mpr
        ⟨_, _, hfin, hWfin _, hdisj, subset_union_left, subset_union_right, hrec, hWmem _⟩
    rw [show (⋃ i, W i) = (⋃ i : Fin k, W i.castSucc) ∪ W (Fin.last k) from
      iUnion_fin_succ W]
    exact hmem

/-- The ambient-configuration form: if the certificates all lie in `ω`, then `ω` itself lies in
the iterated disjoint occurrence. -/
theorem mem_iterDC_of_witnesses {ι : Type*} (k : ℕ) (A : Fin k → Set (Set ι))
    (hA : ∀ i, IsUpperSet (A i)) {ω : Set ι} {W : Fin k → Set ι}
    (hWfin : ∀ i, (W i).Finite) (hWsub : ∀ i, W i ⊆ ω) (hWmem : ∀ i, W i ∈ A i)
    (hWdisj : Pairwise (fun i j => Disjoint (W i) (W j))) : ω ∈ iterDC k A :=
  isUpperSet_iterDC k A hA (Set.iUnion_subset hWsub)
    (iUnion_mem_iterDC_of_witnesses k A hA W hWfin hWmem hWdisj)

/-! ## The measure bound -/

/-- **Nine-singleton BK, abstract form.**  The iterated disjoint occurrence of a `Fin k`-indexed
family of increasing events has probability at most the product of their probabilities, for every
profile on a countable coordinate set.  This is `countable_profile_bk` iterated along the
`iterDC` recursion; it is the `k = 0` counterpart of `sevenGroup_le`. -/
theorem prodBernoulli_iterDC_le {ι : Type*} [Countable ι] (p : ι → unitInterval) :
    ∀ (k : ℕ) (A : Fin k → Set (Set ι)), (∀ i, IsUpperSet (A i)) →
      prodBernoulli p (iterDC k A) ≤ ∏ i : Fin k, prodBernoulli p (A i)
  | 0, _, _ => by simp [iterDC]
  | (k + 1), A, hA => by
    have hbk : prodBernoulli p (iterDC (k + 1) A) ≤
        prodBernoulli p (iterDC k fun i => A i.castSucc) * prodBernoulli p (A (Fin.last k)) :=
      countable_profile_bk p (isUpperSet_iterDC k (fun i => A i.castSucc) fun _ => hA _)
        (hA _)
    have hrec := prodBernoulli_iterDC_le p k (fun i => A i.castSucc) (fun i => hA _)
    calc prodBernoulli p (iterDC (k + 1) A)
        ≤ prodBernoulli p (iterDC k fun i => A i.castSucc) *
            prodBernoulli p (A (Fin.last k)) := hbk
      _ ≤ (∏ i : Fin k, prodBernoulli p (A i.castSucc)) *
            prodBernoulli p (A (Fin.last k)) := mul_le_mul' hrec le_rfl
      _ = ∏ i : Fin (k + 1), prodBernoulli p (A i) := by rw [Fin.prod_univ_castSucc]

/-- **Nine-singleton BK.**  `law π (NineEvent A) ≤ ∏ i, law π (A i)`. -/
theorem law_nineEvent_le {ι : Type*} [Countable ι] (p : ι → unitInterval)
    (A : Fin 9 → Set (Set ι)) (hA : ∀ i, IsUpperSet (A i)) :
    prodBernoulli p (NineEvent A) ≤ ∏ i : Fin 9, prodBernoulli p (A i) :=
  prodBernoulli_iterDC_le p 9 A hA

/-- **Nine-singleton BK, certificate form.**  Nine pairwise disjoint finite open certificates for
increasing events put `ω` in `NineEvent A`. -/
theorem mem_nineEvent_of_witnesses {ι : Type*} (A : Fin 9 → Set (Set ι))
    (hA : ∀ i, IsUpperSet (A i)) {ω : Set ι} {W : Fin 9 → Set ι}
    (hWfin : ∀ i, (W i).Finite) (hWsub : ∀ i, W i ⊆ ω) (hWmem : ∀ i, W i ∈ A i)
    (hWdisj : Pairwise (fun i j => Disjoint (W i) (W j))) : ω ∈ NineEvent A :=
  mem_iterDC_of_witnesses 9 A hA hWfin hWsub hWmem hWdisj

end PercLib.CriticalLRP.TreeExpansion.SixPoint

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.isUpperSet_iterDC
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.iUnion_fin_succ
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.iUnion_mem_iterDC_of_witnesses
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.mem_iterDC_of_witnesses
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.prodBernoulli_iterDC_le
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.law_nineEvent_le
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.mem_nineEvent_of_witnesses
