/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 136, Q-15, item 2). No upstream proof is copied.
-/
module

public import PercLib.Probability.ProdBernoulliIndependence

/-!
# Independence of events determined by disjoint sets of coordinates

An event `A ⊆ Set ι` is determined by `P : Set ι` when `ω ∩ P = ω' ∩ P` implies
`ω ∈ A ↔ ω' ∈ A`. Under `prodBernoulli p`, measurable events determined by disjoint sets of
coordinates are independent, and finitely many measurable events determined by pairwise
disjoint sets of coordinates are mutually independent. No countability is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PercLib.Probability

variable {ι : Type*}

/-- Extending a configuration on `P` by closed coordinates outside `P` is measurable. -/
theorem measurable_image_val (P : Set ι) :
    Measurable (fun η : Set P => (Subtype.val '' η : Set ι)) := by
  classical
  refine Measurable.of_mem fun i => ?_
  by_cases hi : i ∈ P
  · have : (fun η : Set P => i ∈ (Subtype.val '' η : Set ι)) = fun η => ⟨i, hi⟩ ∈ η := by
      funext η
      simp [hi]
    rw [this]
    exact measurable_set_mem _
  · have : (fun η : Set P => i ∈ (Subtype.val '' η : Set ι)) = fun _ => False := by
      funext η
      simp only [mem_image, eq_iff_iff, iff_false, not_exists, not_and]
      rintro ⟨j, hj⟩ _ rfl
      exact hi hj
    rw [this]
    exact measurable_const

/-- A determined event is the preimage, under restriction to `P`, of a measurable set of
configurations on `P`. -/
theorem eq_preimage_restrict_of_determined {P : Set ι} {A : Set (Set ι)}
    (hAP : ∀ ω ω', ω ∩ P = ω' ∩ P → (ω ∈ A ↔ ω' ∈ A)) :
    A = {ω | {i : P | (i : ι) ∈ ω} ∈ (fun η : Set P => (Subtype.val '' η : Set ι)) ⁻¹' A} := by
  ext ω
  refine hAP _ _ ?_
  ext i
  simp only [mem_inter_iff, mem_image, mem_ofPred_eq, Subtype.exists, exists_and_right,
    exists_eq_right]
  constructor
  · rintro ⟨hω, hP⟩
    exact ⟨⟨hP, hω⟩, hP⟩
  · rintro ⟨⟨hP, hω⟩, -⟩
    exact ⟨hω, hP⟩

/-- **Independence of determined events.** Measurable events determined by disjoint sets of
coordinates are independent. -/
theorem prodBernoulli_inter_of_determined (p : ι → unitInterval) {P Q : Set ι}
    (hPQ : Disjoint P Q) {A B : Set (Set ι)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAP : ∀ ω ω', ω ∩ P = ω' ∩ P → (ω ∈ A ↔ ω' ∈ A))
    (hBQ : ∀ ω ω', ω ∩ Q = ω' ∩ Q → (ω ∈ B ↔ ω' ∈ B)) :
    prodBernoulli p (A ∩ B) = prodBernoulli p A * prodBernoulli p B := by
  have h := prodBernoulli_block_inter p P Q hPQ _ _ (hA.preimage (measurable_image_val P))
    (hB.preimage (measurable_image_val Q))
  rw [← eq_preimage_restrict_of_determined hAP, ← eq_preimage_restrict_of_determined hBQ] at h
  convert h using 2
  conv_lhs => rw [eq_preimage_restrict_of_determined hAP, eq_preimage_restrict_of_determined hBQ]
  rfl

/-- An intersection of events determined by subsets of `P` is determined by `P`. -/
theorem determined_biInter {κ : Type*} (s : Finset κ) {P : κ → Set ι} {A : κ → Set (Set ι)}
    {R : Set ι} (hR : ∀ k ∈ s, P k ⊆ R)
    (hA : ∀ k, ∀ ω ω', ω ∩ P k = ω' ∩ P k → (ω ∈ A k ↔ ω' ∈ A k)) :
    ∀ ω ω', ω ∩ R = ω' ∩ R → (ω ∈ ⋂ k ∈ s, A k ↔ ω' ∈ ⋂ k ∈ s, A k) := by
  intro ω ω' h
  simp only [mem_iInter]
  refine forall_congr' fun k => forall_congr' fun hk => hA k ω ω' ?_
  have := congrArg (· ∩ P k) h
  simpa only [inter_assoc, inter_eq_right.2 (hR k hk)] using this

/-- **Finitely many domains.** Measurable events determined by pairwise disjoint sets of
coordinates are mutually independent. -/
theorem prodBernoulli_biInter_of_determined (p : ι → unitInterval) {κ : Type*}
    (s : Finset κ) {P : κ → Set ι} (hP : Set.PairwiseDisjoint (s : Set κ) P)
    {A : κ → Set (Set ι)} (hAm : ∀ k ∈ s, MeasurableSet (A k))
    (hA : ∀ k, ∀ ω ω', ω ∩ P k = ω' ∩ P k → (ω ∈ A k ↔ ω' ∈ A k)) :
    prodBernoulli p (⋂ k ∈ s, A k) = ∏ k ∈ s, prodBernoulli p (A k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have hP' : Set.PairwiseDisjoint (s : Set κ) P :=
      hP.subset (by simp [Set.subset_insert])
    rw [Finset.set_biInter_insert, Finset.prod_insert has,
      prodBernoulli_inter_of_determined p (Q := ⋃ k ∈ s, P k) ?_ (hAm a (by simp))
        (Finset.measurableSet_biInter s fun k hk => hAm k (by simp [hk])) (hA a)
        (determined_biInter s (fun k hk => subset_biUnion_of_mem (u := P) hk) hA),
      ih hP' fun k hk => hAm k (by simp [hk])]
    rw [Set.disjoint_iUnion₂_right]
    intro k hk
    exact hP (by simp) (by simp [hk]) (fun h => has (h ▸ hk))

/-! ### Non-vacuity -/

/-- Two distinct coordinates give determined events with independent probabilities. -/
example (p : Bool → unitInterval) :
    prodBernoulli p ({ω | false ∈ ω} ∩ {ω | true ∈ ω}) =
      prodBernoulli p {ω | false ∈ ω} * prodBernoulli p {ω | true ∈ ω} :=
  prodBernoulli_inter_of_determined p (P := {false}) (Q := {true}) (by simp)
    (measurableSet_mem _) (measurableSet_mem _)
    (fun ω ω' h => by
      have := congrArg (false ∈ ·) h
      simpa using this)
    (fun ω ω' h => by
      have := congrArg (true ∈ ·) h
      simpa using this)

end PercLib.Probability

end
