/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 136, Q-15, items 1, 3 and 4). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Probability.DeterminedIndependence

/-!
# Independence of percolation on disjoint vertex domains

The internal pairs of a vertex set `S` are the unordered pairs with both endpoints in `S`.
Internal pairs of disjoint domains are disjoint, internal connection events of a domain are
determined by its internal pairs, and so events determined by the internal pairs of
pairwise disjoint domains are independent.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Internal pairs of disjoint domains are disjoint. -/
theorem disjoint_internalPairs {S T : Set V} (hST : Disjoint S T) :
    Disjoint {e : Sym2 V | ∀ v ∈ e, v ∈ S} {e : Sym2 V | ∀ v ∈ e, v ∈ T} := by
  rw [Set.disjoint_left]
  intro e hS hT
  induction e using Sym2.ind with
  | _ a b => exact Set.disjoint_left.1 hST (hS a (Sym2.mem_mk_left a b)) (hT a
      (Sym2.mem_mk_left a b))

/-- An internal connection event of `S` is determined by the internal pairs of `S`. -/
theorem localConn_determined (S : Set V) (x y : S) :
    ∀ ω ω' : Config V, ω ∩ {e | ∀ v ∈ e, v ∈ S} = ω' ∩ {e | ∀ v ∈ e, v ∈ S} →
      (ω ∈ {ω : Config V | ((openGraph ω).induce S).Reachable x y} ↔
        ω' ∈ {ω : Config V | ((openGraph ω).induce S).Reachable x y}) := by
  intro ω ω' h
  refine localConn_iff_of_agree S x y fun a ha b hb => ?_
  have hab : s(a, b) ∈ {e : Sym2 V | ∀ v ∈ e, v ∈ S} := by
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ha
    · exact hb
  have := congrArg (s(a, b) ∈ ·) h
  simp only [eq_iff_iff, mem_inter_iff] at this
  constructor
  · intro hω
    exact (this.1 ⟨hω, hab⟩).1
  · intro hω
    exact (this.2 ⟨hω, hab⟩).1

/-- Measurable events determined by the internal pairs of disjoint domains are independent. -/
theorem law_inter_of_determined_internalPairs (q : Sym2 V → unitInterval) {S T : Set V}
    (hST : Disjoint S T) {A B : Set (Config V)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : ∀ ω ω' : Config V, ω ∩ {e | ∀ v ∈ e, v ∈ S} = ω' ∩ {e | ∀ v ∈ e, v ∈ S} →
      (ω ∈ A ↔ ω' ∈ A))
    (hBT : ∀ ω ω' : Config V, ω ∩ {e | ∀ v ∈ e, v ∈ T} = ω' ∩ {e | ∀ v ∈ e, v ∈ T} →
      (ω ∈ B ↔ ω' ∈ B)) :
    law q (A ∩ B) = law q A * law q B :=
  prodBernoulli_inter_of_determined q (disjoint_internalPairs hST) hA hB hAS hBT

/-- **Internal connections in disjoint domains are independent.** -/
theorem law_localConn_inter_eq_mul (q : Sym2 V → unitInterval) {S T : Set V}
    [Countable S] [Countable T] (hST : Disjoint S T) (x y : S) (u v : T) :
    law q {ω | ((openGraph ω).induce S).Reachable x y ∧
        ((openGraph ω).induce T).Reachable u v} =
      law q {ω | ((openGraph ω).induce S).Reachable x y} *
        law q {ω | ((openGraph ω).induce T).Reachable u v} :=
  law_inter_of_determined_internalPairs q hST (measurableSet_localConn S x y)
    (measurableSet_localConn T u v) (localConn_determined S x y) (localConn_determined T u v)

/-- **Finitely many domains.** Measurable events determined by the internal pairs of
pairwise disjoint domains are mutually independent. -/
theorem law_biInter_of_determined_internalPairs (q : Sym2 V → unitInterval) {κ : Type*}
    (s : Finset κ) {S : κ → Set V} (hS : Set.PairwiseDisjoint (s : Set κ) S)
    {A : κ → Set (Config V)} (hAm : ∀ k ∈ s, MeasurableSet (A k))
    (hA : ∀ k, ∀ ω ω' : Config V,
      ω ∩ {e | ∀ v ∈ e, v ∈ S k} = ω' ∩ {e | ∀ v ∈ e, v ∈ S k} → (ω ∈ A k ↔ ω' ∈ A k)) :
    law q (⋂ k ∈ s, A k) = ∏ k ∈ s, law q (A k) :=
  prodBernoulli_biInter_of_determined q s
    (fun _ hk _ hl hkl => disjoint_internalPairs (hS hk hl hkl)) hAm hA

/-- The same for a family indexed by `Fin n`. -/
theorem law_iInter_fin_of_determined_internalPairs (q : Sym2 V → unitInterval) {n : ℕ}
    {S : Fin n → Set V} (hS : Pairwise fun i j => Disjoint (S i) (S j))
    {A : Fin n → Set (Config V)} (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, ∀ ω ω' : Config V,
      ω ∩ {e | ∀ v ∈ e, v ∈ S i} = ω' ∩ {e | ∀ v ∈ e, v ∈ S i} → (ω ∈ A i ↔ ω' ∈ A i)) :
    law q (⋂ i, A i) = ∏ i, law q (A i) := by
  have h := law_biInter_of_determined_internalPairs q Finset.univ
    (fun _ _ _ _ hij => hS hij) (fun i _ => hAm i) hA
  simpa using h

/-! ### Non-vacuity -/

/-- Two disjoint domains of `Fin 4` with the constant profile `1/2`. -/
example :
    law (fun _ : Sym2 (Fin 4) => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
        {ω | ((openGraph ω).induce ({0, 1} : Set (Fin 4))).Reachable ⟨0, by simp⟩ ⟨1, by simp⟩ ∧
          ((openGraph ω).induce ({2, 3} : Set (Fin 4))).Reachable ⟨2, by simp⟩ ⟨3, by simp⟩} =
      law (fun _ : Sym2 (Fin 4) => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
          {ω | ((openGraph ω).induce ({0, 1} : Set (Fin 4))).Reachable ⟨0, by simp⟩ ⟨1, by simp⟩} *
        law (fun _ : Sym2 (Fin 4) => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
          {ω | ((openGraph ω).induce ({2, 3} : Set (Fin 4))).Reachable ⟨2, by simp⟩ ⟨3, by simp⟩} :=
  law_localConn_inter_eq_mul _ (by
    rw [Set.disjoint_left]
    intro a ha hb
    simp only [mem_insert_iff, mem_singleton_iff] at ha hb
    omega) _ _ _ _

end PercLib.Percolation.Bond

end
