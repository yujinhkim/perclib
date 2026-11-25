/- Integrated from reviewed Ultramath combinatorics.
Production base e387aba5a75e414ca007951b6333ffa5af720573.
Scratch source: ../../.ultramath/smwvlmbqa/m1/Bridge.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Atlas.Edges

/-!
# Hub sets on production vertices (`RTree.IPos`) and their atlas edge sets

`Hub.lean` selects hub sets among the *addresses* `ipaths t` of the internal vertices of a
production tree `t : RTree α`.  This file identifies those addresses with production's
internal-vertex type `RTree.IPos t`:

* `RTree.iposOfPath` descends to the vertex at an address,
* `RTree.pathOf` returns the address of a vertex,
* `RTree.iposOfPath_pathOf` and `RTree.pathOf_iposOfPath` are the two round trips, giving the
  equivalence `RTree.exists_iposEquiv` and the cardinality bridge
  `RTree.card_ipos_eq_card_ipaths`.

Consequently the hub set of Lemma I.4.16 can be taken to be a `Finset (IPos t)` of *production
vertices* (`exists_hubSet_ipos`), still of one depth parity, with pairwise disjoint 3-stars
(`card_hubEdgesIpos`: exactly `3k` atlas edges) and `2p - 1 - 3k` unused edges
(`card_offHubEdgesIpos`), the two parts partitioning the atlas
(`exists_hub_edge_partition_ipos`).
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

/-! ### From addresses to vertices and back -/

/-- **First round trip**: the address of the vertex at an address is that address. -/
theorem pathOf_iposOfPath : ∀ (t : RTree α) (s : List Bool) (hs : s ∈ ipaths t),
    (pathOf t (iposOfPath t s hs)).1 = s := by
  intro t
  induction t with
  | leaf a =>
      intro s hs
      simp [ipaths] at hs
  | node l r ihl ihr =>
      intro s hs
      match s with
      | [] => rfl
      | false :: s0 =>
          change (false :: (pathOf l (iposOfPath l s0 _)).1) = false :: s0
          rw [ihl]
      | true :: s0 =>
          change (true :: (pathOf r (iposOfPath r s0 _)).1) = true :: s0
          rw [ihr]

/-- **Second round trip**: the vertex at the address of a vertex is that vertex. -/
theorem iposOfPath_pathOf : ∀ (t : RTree α) (v : IPos t),
    iposOfPath t (pathOf t v).1 (pathOf t v).2 = v := by
  intro t
  induction t with
  | leaf a =>
      intro v
      exact Empty.elim v
  | node l r ihl ihr =>
      intro v
      match v with
      | Sum.inl a =>
          change Sum.inl (iposOfPath l (pathOf l a).1 (pathOf l a).2) = Sum.inl a
          rw [ihl]
      | Sum.inr (Sum.inl b) =>
          change Sum.inr (Sum.inl (iposOfPath r (pathOf r b).1 (pathOf r b).2)) =
            Sum.inr (Sum.inl b)
          rw [ihr]
      | Sum.inr (Sum.inr u) =>
          rfl

/-- The internal vertices of `t` are its internal addresses: the two round trips exhibit the
bijection.  (Stated as an existence, not as a named `Equiv`, so that `Defs.lean` carries every
new definition of this layer.) -/
theorem exists_iposEquiv (t : RTree α) :
    ∃ e : {s : List Bool // s ∈ ipaths t} ≃ IPos t, ∀ p, e p = iposOfPath t p.1 p.2 :=
  ⟨{ toFun := fun p => iposOfPath t p.1 p.2
     invFun := pathOf t
     left_inv := fun p => Subtype.ext (by simpa using pathOf_iposOfPath t p.1 p.2)
     right_inv := fun v => iposOfPath_pathOf t v }, fun _ => rfl⟩

/-- **Cardinality bridge**: production's internal-vertex count is the count of internal
addresses. -/
theorem card_ipos_eq_card_ipaths (t : RTree α) :
    Fintype.card (IPos t) = (ipaths t).card := by
  rw [card_ipos, card_ipaths]

/-- The two orientations of the round trip, in the form used below. -/
theorem pathOf_injective (t : RTree α) {v w : IPos t} (h : pathOf t v = pathOf t w) : v = w := by
  have h2 : iposOfPath t (pathOf t v).1 (pathOf t v).2 =
      iposOfPath t (pathOf t w).1 (pathOf t w).2 :=
    congrArg (fun p : {s : List Bool // s ∈ ipaths t} => iposOfPath t p.1 p.2) h
  rw [iposOfPath_pathOf, iposOfPath_pathOf] at h2
  exact h2

/-! ### Depth parity of a vertex -/

theorem iposDepth_iposOfPath (t : RTree α) (s : List Bool) (hs : s ∈ ipaths t) :
    iposDepth t (iposOfPath t s hs) = s.length := by
  rw [iposDepth, pathOf_iposOfPath]

theorem card_iposEvenHubs_add_card_iposOddHubs (t : RTree α) :
    (iposEvenHubs t).card + (iposOddHubs t).card = Fintype.card (IPos t) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (IPos t))) (p := fun v => iposDepth t v % 2 = 0)
  have hodd : (Finset.univ.filter (fun v : IPos t => ¬ iposDepth t v % 2 = 0)) =
      iposOddHubs t := by
    rw [iposOddHubs]
    refine Finset.filter_congr fun v _ => ?_
    have := Nat.mod_two_eq_zero_or_one (iposDepth t v)
    omega
  rw [iposEvenHubs, ← hodd, hsplit, Finset.card_univ]

/-- The larger bipartition class of the internal vertices of the atlas has at least
`⌈(p-1)/2⌉` elements. -/
theorem ceil_half_le_max_ipos_class (t : RTree α) :
    (t.numLeaves - 1 + 1) / 2 ≤ max (iposEvenHubs t).card (iposOddHubs t).card := by
  have h := card_iposEvenHubs_add_card_iposOddHubs t
  rw [card_ipos_eq_card_ipaths, card_ipaths] at h
  have key : (iposEvenHubs t).card + (iposOddHubs t).card ≤
      2 * max (iposEvenHubs t).card (iposOddHubs t).card := by
    have := le_max_left (iposEvenHubs t).card (iposOddHubs t).card
    have := le_max_right (iposEvenHubs t).card (iposOddHubs t).card
    omega
  omega

/-- **Hub selection among production vertices.**  For `k ≤ ⌈(p-1)/2⌉` there are `k` internal
vertices of `t`, all of the same depth parity, i.e. pairwise non-adjacent in the atlas. -/
theorem exists_hubSet_ipos (t : RTree α) {k : ℕ}
    (hk : k ≤ (t.numLeaves - 1 + 1) / 2) :
    ∃ S : Finset (IPos t), S.card = k ∧
      ((∀ v ∈ S, iposDepth t v % 2 = 0) ∨ (∀ v ∈ S, iposDepth t v % 2 = 1)) := by
  have hmax := ceil_half_le_max_ipos_class t
  rcases le_total (iposEvenHubs t).card (iposOddHubs t).card with hab | hab
  · have hkb : k ≤ (iposOddHubs t).card :=
      le_trans hk (le_trans hmax (le_of_eq (max_eq_right hab)))
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := iposOddHubs t) hkb
    refine ⟨S, hScard, Or.inr fun v hv => ?_⟩
    exact (Finset.mem_filter.mp (hSsub hv)).2
  · have hka : k ≤ (iposEvenHubs t).card :=
      le_trans hk (le_trans hmax (le_of_eq (max_eq_left hab)))
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := iposEvenHubs t) hka
    refine ⟨S, hScard, Or.inl fun v hv => ?_⟩
    exact (Finset.mem_filter.mp (hSsub hv)).2

/-! ### The 3-stars at a hub set of production vertices -/

theorem mem_hubEdgesIpos {t : RTree α} {S : Finset (IPos t)} {e : AtlasEdge t} :
    e ∈ hubEdgesIpos t S ↔
      ∃ (v : IPos t), v ∈ S ∧ e ∈ star t (pathOf t v).1 (pathOf t v).2 := by
  rw [hubEdgesIpos, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, -, hv⟩
    exact ⟨v.1, v.2, hv⟩
  · rintro ⟨v, hv, he⟩
    exact ⟨⟨v, hv⟩, Finset.mem_attach _ _, he⟩

/-- **`3k` edges.**  If the hubs all have the same depth parity, their 3-stars are pairwise
disjoint, so they use exactly `3 · #S` atlas edges. -/
theorem card_hubEdgesIpos (t : RTree α) (S : Finset (IPos t))
    (hpar : (∀ v ∈ S, iposDepth t v % 2 = 0) ∨ (∀ v ∈ S, iposDepth t v % 2 = 1)) :
    (hubEdgesIpos t S).card = 3 * S.card := by
  have hsame : ∀ a ∈ S, ∀ b ∈ S, (pathOf t a).1.length % 2 = (pathOf t b).1.length % 2 := by
    intro a ha b hb
    rw [show (pathOf t a).1.length = iposDepth t a from rfl,
      show (pathOf t b).1.length = iposDepth t b from rfl]
    rcases hpar with h | h
    · rw [h a ha, h b hb]
    · rw [h a ha, h b hb]
  have hpd : (S.attach : Set {x // x ∈ S}).PairwiseDisjoint
      (fun p => star t (pathOf t p.1).1 (pathOf t p.1).2) := by
    intro a _ b _ hab
    have hne : (pathOf t a.1).1 ≠ (pathOf t b.1).1 := by
      intro hc
      exact hab (Subtype.ext (pathOf_injective t (Subtype.ext hc)))
    exact star_disjoint (pathOf t a.1).2 (pathOf t b.1).2 hne (hsame a.1 a.2 b.1 b.2)
  rw [hubEdgesIpos, Finset.card_biUnion hpd]
  have h3 : ∀ p ∈ S.attach, (star t (pathOf t p.1).1 (pathOf t p.1).2).card = 3 :=
    fun p _ => card_star (pathOf t p.1).2
  rw [Finset.sum_congr rfl h3, Finset.sum_const_nat (fun _ _ => rfl), Finset.card_attach]
  ring

/-- **The remaining edges.**  A hub set of `k` internal vertices of one parity class leaves
exactly `2p - 1 - 3k` atlas edges not adjacent to it. -/
theorem card_offHubEdgesIpos (t : RTree α) (S : Finset (IPos t))
    (hpar : (∀ v ∈ S, iposDepth t v % 2 = 0) ∨ (∀ v ∈ S, iposDepth t v % 2 = 1)) :
    (offHubEdgesIpos t S).card = 2 * t.numLeaves - 1 - 3 * S.card := by
  rw [offHubEdgesIpos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    card_atlasEdge_leaves, card_hubEdgesIpos t S hpar]

/-- **The deselection step of Lemma I.4.16 on production vertices, packaged.**

For every atlas with `p` leaves and every `k ≤ ⌈(p-1)/2⌉` there are `k` internal vertices of
`t` in a single bipartition class whose 3-stars are pairwise disjoint and use exactly `3k` of
the `2p - 1` atlas edges, the remaining `2p - 1 - 3k` edges not being adjacent to any of them;
the two edge sets partition the atlas. -/
theorem exists_hub_edge_partition_ipos (t : RTree α) {k : ℕ}
    (hk : k ≤ (t.numLeaves - 1 + 1) / 2) :
    ∃ S : Finset (IPos t), S.card = k ∧
      ((∀ v ∈ S, iposDepth t v % 2 = 0) ∨ (∀ v ∈ S, iposDepth t v % 2 = 1)) ∧
      (hubEdgesIpos t S).card = 3 * k ∧
      (offHubEdgesIpos t S).card = 2 * t.numLeaves - 1 - 3 * k ∧
      hubEdgesIpos t S ∪ offHubEdgesIpos t S = Finset.univ ∧
      Disjoint (hubEdgesIpos t S) (offHubEdgesIpos t S) := by
  obtain ⟨S, hcard, hpar⟩ := exists_hubSet_ipos t hk
  refine ⟨S, hcard, hpar, ?_, ?_, ?_, ?_⟩
  · rw [card_hubEdgesIpos t S hpar, hcard]
  · rw [card_offHubEdgesIpos t S hpar, hcard]
  · rw [offHubEdgesIpos]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
  · rw [offHubEdgesIpos]
    exact Finset.disjoint_sdiff

/-- **The two child arms of a hub.**  Every internal vertex of `t` has an address, and at that
address `t` splits into a left and a right subtree: the two downward arms of the 3-star, whose
leaf sets are the two arms used by the three-fold BK step. -/
theorem exists_children_of_ipos (t : RTree α) (v : IPos t) :
    ∃ l r : RTree α, subAt t (pathOf t v).1 = some (node l r) :=
  (mem_ipaths t (pathOf t v).1).mp (pathOf t v).2

end RTree

end PercLib.CriticalLRP.TreeExpansion
