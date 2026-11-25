/- Integrated from reviewed Ultramath combinatorics.
Production base e387aba5a75e414ca007951b6333ffa5af720573.
Scratch source: ../../.ultramath/smwvlmbqa/m1/Edges.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Atlas.Hub

/-!
# The edge partition of the atlas at a hub set

For `t : RTree α` with `p = t.numLeaves`, the atlas of `t` has `2p - 1` edges
(`card_atlasEdge_leaves`).  For a hub set `S` of internal vertices all of one depth parity,
the 3-stars at the hubs are pairwise disjoint and cover exactly `3 · #S` edges; the remaining
`2p - 1 - 3 · #S` atlas edges are exactly the edges not adjacent to the hub set.  The paper
calls these "the remaining edges of the tree that are not adjacent to a vertex in this set".

Here the two parts are exhibited as an honest partition of `Finset.univ` of the edge type
(`hubEdges_union_offHubEdges`, `disjoint_hubEdges_offHubEdges`), with the two cardinalities
`3k` and `2p - 1 - 3k` (`card_hubEdges`, `card_offHubEdges`).  This is the deterministic
input to the BK step of Lemma I.4.16: `k` of the factors become three-point (in-cluster)
functions and the other `2p - 1 - 3k` become two-point functions.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

/-- **`#E = 2p - 1`** for the atlas of a tree with `p` leaves. -/
theorem card_atlasEdge_leaves (t : RTree α) :
    Fintype.card (AtlasEdge t) = 2 * t.numLeaves - 1 := by
  rw [card_atlasEdge, card_ipaths]
  have := numLeaves_pos t
  omega

theorem mem_hubEdges {t : RTree α} {S : Finset (List Bool)} {hS : S ⊆ ipaths t}
    {e : AtlasEdge t} :
    e ∈ hubEdges t S hS ↔ ∃ (s : List Bool) (hs : s ∈ S), e ∈ star t s (hS hs) := by
  rw [hubEdges, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, -, hv⟩
    exact ⟨v.1, v.2, hv⟩
  · rintro ⟨s, hs, hs'⟩
    exact ⟨⟨s, hs⟩, Finset.mem_attach _ _, hs'⟩

theorem mem_offHubEdges {t : RTree α} {S : Finset (List Bool)} {hS : S ⊆ ipaths t}
    {e : AtlasEdge t} :
    e ∈ offHubEdges t S hS ↔ ¬ ∃ (s : List Bool) (hs : s ∈ S), e ∈ star t s (hS hs) := by
  rw [offHubEdges, Finset.mem_sdiff, mem_hubEdges]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The hub edges and the remaining edges partition the atlas. -/
theorem hubEdges_union_offHubEdges (t : RTree α) (S : Finset (List Bool))
    (hS : S ⊆ ipaths t) :
    hubEdges t S hS ∪ offHubEdges t S hS = Finset.univ := by
  rw [offHubEdges]
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

theorem disjoint_hubEdges_offHubEdges (t : RTree α) (S : Finset (List Bool))
    (hS : S ⊆ ipaths t) : Disjoint (hubEdges t S hS) (offHubEdges t S hS) := by
  rw [offHubEdges]
  exact Finset.disjoint_sdiff

/-- **The remaining edges**: exactly `2p - 1 - 3k` atlas edges are not adjacent to a hub set
of size `k` lying in a single bipartition class. -/
theorem card_offHubEdges (t : RTree α) (S : Finset (List Bool)) (hS : S ⊆ ipaths t)
    (hpar : S ⊆ evenHubs t ∨ S ⊆ oddHubs t) {k : ℕ} (hcard : S.card = k) :
    (offHubEdges t S hS).card = 2 * t.numLeaves - 1 - 3 * k := by
  rw [offHubEdges, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    card_atlasEdge_leaves, card_hubEdges t S hS hpar, hcard]

/-- **The edge partition at a hub set, packaged.**  For every atlas with `p` leaves and
every `k ≤ ⌈(p-1)/2⌉` there is a hub set of `k` internal vertices in one bipartition class
whose 3-stars use exactly `3k` of the `2p - 1` atlas edges, leaving exactly `2p - 1 - 3k`
edges, and these two edge sets partition the atlas. -/
theorem exists_hub_edge_partition (t : RTree α) {k : ℕ}
    (hk : k ≤ (t.numLeaves - 1 + 1) / 2) :
    ∃ (S : Finset (List Bool)) (hS : S ⊆ ipaths t), S.card = k ∧
      (S ⊆ evenHubs t ∨ S ⊆ oddHubs t) ∧
      (hubEdges t S hS).card = 3 * k ∧
      (offHubEdges t S hS).card = 2 * t.numLeaves - 1 - 3 * k ∧
      hubEdges t S hS ∪ offHubEdges t S hS = Finset.univ ∧
      Disjoint (hubEdges t S hS) (offHubEdges t S hS) := by
  obtain ⟨S, hS, hcard, hpar⟩ := exists_hubSet t hk
  refine ⟨S, hS, hcard, hpar, ?_, ?_, ?_, ?_⟩
  · rw [card_hubEdges t S hS hpar, hcard]
  · exact card_offHubEdges t S hS hpar hcard
  · exact hubEdges_union_offHubEdges t S hS
  · exact disjoint_hubEdges_offHubEdges t S hS

end RTree

end PercLib.CriticalLRP.TreeExpansion
