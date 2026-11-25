/- Integrated from reviewed Ultramath combinatorics.
Production base e387aba5a75e414ca007951b6333ffa5af720573.
Scratch source: ../../.ultramath/smwvlmbqa/m1/Hub.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.Atlas.Defs

/-!
# The bipartite-class / hub-selection step of Lemma I.4.16

`Lemma I.4.16` (generalized tree-graph inequality) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, pp. 43--45

improves the ordinary tree-graph moment bound `E|K|^p ≤ (2p-3)!! (E|K|)^{2p-1}` to

  `E|K|^p ≤ (2p-3)!! (E|K|^2)^k (E|K|)^{2p-1-3k}`,   `0 ≤ k ≤ ⌈(p-1)/2⌉`.

The combinatorial content of the improvement is the following.  An atlas (a binary tree with
`p - 1` internal vertices, `p` labelled non-root leaves and the root leaf `0`) has `2p - 1`
edges; the paper

* bipartitions the internal vertices by depth parity, so that the larger class has at least
  `⌈(p-1)/2⌉` elements;
* picks `k ≤ ⌈(p-1)/2⌉` of them, all of one class, and "partitions the edges of the tree
  into the 3-stars around each vertex in this set and the remaining edges of the tree that
  are not adjacent to a vertex in this set";
* then applies the BK inequality to each star, which after summing gives `k` copies of a
  two-point (in-cluster) function and `2p - 1 - 3k` copies of the two-point function.

This file proves, for every `p ≥ 1`, every atlas `t` with `p` leaves and every
`k ≤ ⌈(p-1)/2⌉`:

* `exists_hubSet` — there is a hub set `S` of `k` internal vertices lying in a single
  bipartite class;
* `card_biUnion_star` — the 3-stars of the vertices of `S` are pairwise disjoint and use
  exactly `3k` of the `2p - 1` atlas edges (`card_atlasEdge`);
* `card_edges_off_hubs` — consequently exactly `2p - 1 - 3k` atlas edges are *not* incident
  with `S`; these are the "remaining edges" of the paper;
* `leaf_arm_partition` — the three arms of the star at a hub lead to three pairwise
  disjoint, nonempty sets of leaves; this is the deterministic input to the three-fold BK
  step at a hub.

Everything here is finite combinatorics: no probability enters.
-/

@[expose] public section

set_option autoImplicit false

open Finset

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

/-! ### Cardinalities of the vertex sets -/

theorem cons_false_inj : Function.Injective (fun s : List Bool => false :: s) := by
  intro a b h
  simpa using h

theorem cons_true_inj : Function.Injective (fun s : List Bool => true :: s) := by
  intro a b h
  simpa using h

theorem disjoint_cons_image (A B : Finset (List Bool)) :
    Disjoint (A.image (fun s => false :: s)) (B.image (fun s => true :: s)) := by
  refine Finset.disjoint_left.mpr fun x hx hy => ?_
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
  simp at hb

theorem not_mem_cons_image (A : Finset (List Bool)) (b : Bool) :
    ([] : List Bool) ∉ A.image (fun s => b :: s) := by
  simp

/-- The number of leaves of the `RTree` is the number of its leaf addresses. -/
theorem card_lpaths (t : RTree α) : (lpaths t).card = t.numLeaves := by
  induction t with
  | leaf a => simp [lpaths, numLeaves]
  | node l r ihl ihr =>
      have h1 : (lpaths (node l r)).card
          = ((lpaths l).image (fun s => false :: s)).card
            + ((lpaths r).image (fun s => true :: s)).card := by
        simp only [lpaths]
        rw [Finset.card_union_of_disjoint (disjoint_cons_image _ _)]
      rw [h1, Finset.card_image_of_injective _ cons_false_inj,
        Finset.card_image_of_injective _ cons_true_inj, ihl, ihr, numLeaves_node]

/-- A tree with `p` leaves has `p - 1` internal vertices. -/
theorem card_ipaths (t : RTree α) : (ipaths t).card = t.numLeaves - 1 := by
  induction t with
  | leaf a => simp [ipaths]
  | node l r ihl ihr =>
      have hd : Disjoint ((ipaths l).image (fun s => false :: s))
          ((ipaths r).image (fun s => true :: s)) := disjoint_cons_image _ _
      have hnil : ([] : List Bool) ∉ ((ipaths l).image (fun s => false :: s) ∪
          (ipaths r).image (fun s => true :: s)) := by simp
      have h1 : (ipaths (node l r)).card
          = 1 + ((ipaths l).image (fun s => false :: s)).card
            + ((ipaths r).image (fun s => true :: s)).card := by
        simp only [ipaths]
        rw [Finset.card_insert_of_notMem hnil, Finset.card_union_of_disjoint hd]
        omega
      rw [h1, Finset.card_image_of_injective _ cons_false_inj,
        Finset.card_image_of_injective _ cons_true_inj, ihl, ihr, numLeaves_node]
      have hl := numLeaves_pos l
      have hr := numLeaves_pos r
      omega

/-! ### The two bipartite classes -/

theorem evenHubs_subset (t : RTree α) : evenHubs t ⊆ ipaths t := Finset.filter_subset _ _

theorem oddHubs_subset (t : RTree α) : oddHubs t ⊆ ipaths t := Finset.filter_subset _ _

/-- Every internal vertex is of even or of odd depth, so the two classes cover `ipaths`. -/
theorem ipaths_subset_even_union_odd (t : RTree α) :
    ipaths t ⊆ evenHubs t ∪ oddHubs t := by
  intro s hs
  have h2 : s.length % 2 = 0 ∨ s.length % 2 = 1 := Nat.mod_two_eq_zero_or_one s.length
  rcases h2 with h | h
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, h⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, h⟩)

theorem disjoint_evenHubs_oddHubs (t : RTree α) : Disjoint (evenHubs t) (oddHubs t) := by
  refine Finset.disjoint_left.mpr fun s h1 h2 => ?_
  rw [evenHubs, Finset.mem_filter] at h1
  rw [oddHubs, Finset.mem_filter] at h2
  omega

/-- `#even + #odd = #internal = p - 1`. -/
theorem card_evenHubs_add_card_oddHubs (t : RTree α) :
    (evenHubs t).card + (oddHubs t).card = t.numLeaves - 1 := by
  have hunion : evenHubs t ∪ oddHubs t = ipaths t :=
    Finset.Subset.antisymm (Finset.union_subset (evenHubs_subset t) (oddHubs_subset t))
      (ipaths_subset_even_union_odd t)
  rw [← Finset.card_union_of_disjoint (disjoint_evenHubs_oddHubs t), hunion, card_ipaths]

/-- The larger of the two bipartite classes has at least `⌈(p-1)/2⌉` elements. -/
theorem ceil_half_le_max_class (t : RTree α) :
    (t.numLeaves - 1 + 1) / 2 ≤ max (evenHubs t).card (oddHubs t).card := by
  set a := (evenHubs t).card
  set b := (oddHubs t).card
  have h := card_evenHubs_add_card_oddHubs t
  have hmax : a ≤ max a b := le_max_left _ _
  have hmax' : b ≤ max a b := le_max_right _ _
  have key : a + b ≤ 2 * max a b := by omega
  have h2 : (a + b + 1) / 2 ≤ max a b := by omega
  omega

/-! ### Hub selection -/

/-- **The hub set of Lemma I.4.16.**  Given `k ≤ ⌈(p-1)/2⌉` there are `k` internal vertices
of the atlas, all of the same depth parity — so no two of them are adjacent. -/
theorem exists_hubSet (t : RTree α) {k : ℕ}
    (hk : k ≤ (t.numLeaves - 1 + 1) / 2) :
    ∃ S : Finset (List Bool), S ⊆ ipaths t ∧ S.card = k ∧
      (S ⊆ evenHubs t ∨ S ⊆ oddHubs t) := by
  set a := (evenHubs t).card
  set b := (oddHubs t).card
  have hmax := ceil_half_le_max_class t
  rcases le_total a b with hab | hab
  · have hkb : k ≤ b := le_trans hk (le_trans hmax (le_of_eq (max_eq_right hab)))
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := oddHubs t) hkb
    exact ⟨S, fun x hx => oddHubs_subset t (hSsub hx), hScard, Or.inr hSsub⟩
  · have hka : k ≤ a := le_trans hk (le_trans hmax (le_of_eq (max_eq_left hab)))
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := evenHubs t) hka
    exact ⟨S, fun x hx => evenHubs_subset t (hSsub hx), hScard, Or.inl hSsub⟩

/-! ### The 3-stars are disjoint and use `3k` edges -/

/-- `s` is one longer than its parent. -/
theorem length_eq_dropLast_succ {s : List Bool} (h : s ≠ []) :
    s.length = s.dropLast.length + 1 := by
  conv_lhs => rw [← List.dropLast_append_getLast h]
  simp

theorem mod_two_ne_mod_two_succ (n : ℕ) : n % 2 ≠ (n + 1) % 2 := by
  omega

/-- A down edge determines its child: two down edges coincide only if their child addresses
and bits do. -/
theorem downEdge_inj {t : RTree α} {s s' : List Bool} {hs : s ∈ ipaths t}
    {hs' : s' ∈ ipaths t} {b b' : Bool}
    (h : (Sum.inl (⟨s, hs⟩, b) : AtlasEdge t) = Sum.inl (⟨s', hs'⟩, b')) :
    s = s' ∧ b = b' := by
  have h2 : ((⟨s, hs⟩, b) : {u : List Bool // u ∈ ipaths t} × Bool) =
      ((⟨s', hs'⟩, b') : {u : List Bool // u ∈ ipaths t} × Bool) := Sum.inl.inj h
  rw [Prod.mk.injEq] at h2
  exact ⟨congrArg Subtype.val h2.1, h2.2⟩

theorem upEdge_nil {t : RTree α} (hs : ([] : List Bool) ∈ ipaths t) :
    upEdge t [] hs = Sum.inr ⟨⟩ := by
  unfold upEdge
  split
  · rfl
  · rename_i hh
    exact absurd rfl hh

theorem upEdge_cons {t : RTree α} {s : List Bool} (hs : s ∈ ipaths t) (h : s ≠ []) :
    upEdge t s hs =
      (Sum.inl ((⟨s.dropLast, dropLast_mem_ipaths hs h⟩, s.getLast h) :
        {u : List Bool // u ∈ ipaths t} × Bool) : AtlasEdge t) := by
  unfold upEdge
  split
  · rename_i hh
    exact absurd hh h
  · rfl

/-- The up edge determines its lower endpoint. -/
theorem upEdge_inj {t : RTree α} {s s' : List Bool} (hs : s ∈ ipaths t)
    (hs' : s' ∈ ipaths t) (h : upEdge t s hs = upEdge t s' hs') : s = s' := by
  by_cases h1 : s = []
  · subst h1
    by_cases h2 : s' = []
    · rw [h2]
    · rw [upEdge_nil hs, upEdge_cons hs' h2] at h
      exact absurd h (by simp)
  · by_cases h2 : s' = []
    · subst h2
      rw [upEdge_nil hs', upEdge_cons hs h1, eq_comm] at h
      exact absurd h (by simp)
    · rw [upEdge_cons hs h1, upEdge_cons hs' h2] at h
      have h3 : ((⟨s.dropLast, _⟩, s.getLast h1) : {u : List Bool // u ∈ ipaths t} × Bool) =
          ((⟨s'.dropLast, _⟩, s'.getLast h2) : {u : List Bool // u ∈ ipaths t} × Bool) :=
        Sum.inl.inj h
      rw [Prod.mk.injEq] at h3
      have hv : s.dropLast = s'.dropLast := congrArg Subtype.val h3.1
      rw [← List.dropLast_append_getLast h1, ← List.dropLast_append_getLast h2, hv, h3.2]

/-- A down edge coincides with an up edge only if it is the up edge of a child of its lower
endpoint. -/
theorem downEdge_eq_upEdge {t : RTree α} {s s' : List Bool} (hs : s ∈ ipaths t)
    (hs' : s' ∈ ipaths t) {b : Bool}
    (h : (Sum.inl (⟨s, hs⟩, b) : AtlasEdge t) = upEdge t s' hs') :
    ∃ (hne : s' ≠ []), s = s'.dropLast ∧ b = s'.getLast hne := by
  by_cases h2 : s' = []
  · subst h2
    rw [upEdge_nil hs'] at h
    exact absurd h (by simp)
  · rw [upEdge_cons hs' h2] at h
    have h3 : ((⟨s, hs⟩, b) : {u : List Bool // u ∈ ipaths t} × Bool) =
        ((⟨s'.dropLast, _⟩, s'.getLast h2) : {u : List Bool // u ∈ ipaths t} × Bool) :=
      Sum.inl.inj h
    rw [Prod.mk.injEq] at h3
    exact ⟨h2, congrArg Subtype.val h3.1, h3.2⟩

theorem upEdge_eq_downEdge {t : RTree α} {s s' : List Bool} (hs : s ∈ ipaths t)
    (hs' : s' ∈ ipaths t) {b : Bool}
    (h : upEdge t s hs = (Sum.inl (⟨s', hs'⟩, b) : AtlasEdge t)) :
    ∃ (hne : s ≠ []), s' = s.dropLast ∧ b = s.getLast hne := by
  by_cases h1 : s = []
  · subst h1
    rw [upEdge_nil hs] at h
    exact absurd h (by simp)
  · rw [upEdge_cons hs h1] at h
    have h3 : ((⟨s.dropLast, _⟩, s.getLast h1) : {u : List Bool // u ∈ ipaths t} × Bool) =
        ((⟨s', hs'⟩, b) : {u : List Bool // u ∈ ipaths t} × Bool) := Sum.inl.inj h
    rw [Prod.mk.injEq] at h3
    exact ⟨h1, (congrArg Subtype.val h3.1).symm, h3.2.symm⟩

/-- Two 3-stars can meet only if their hubs coincide or one hub is the parent of the
other. -/
theorem star_not_disjoint_imp {t : RTree α} {s s' : List Bool} (hs : s ∈ ipaths t)
    (hs' : s' ∈ ipaths t) (h : ¬ Disjoint (star t s hs) (star t s' hs')) :
    s = s' ∨ s = s'.dropLast ∨ s' = s.dropLast := by
  obtain ⟨e, h1, h2⟩ := Finset.not_disjoint_iff.mp h
  rw [mem_star] at h1 h2
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2
  · exact Or.inl (downEdge_inj h2).1
  · exact absurd (downEdge_inj h2).2 (by simp)
  · exact Or.inr (Or.inl (downEdge_eq_upEdge hs hs' h2).2.1)
  · exact absurd (downEdge_inj h2).2 (by simp)
  · exact Or.inl (downEdge_inj h2).1
  · exact Or.inr (Or.inl (downEdge_eq_upEdge hs hs' h2).2.1)
  · exact Or.inr (Or.inr (upEdge_eq_downEdge hs hs' h2).2.1)
  · exact Or.inr (Or.inr (upEdge_eq_downEdge hs hs' h2).2.1)
  · exact Or.inl (upEdge_inj hs hs' h2)

/-- **Disjointness of the 3-stars of a hub set of one parity class.** -/
theorem star_disjoint {t : RTree α} {s s' : List Bool} (hs : s ∈ ipaths t)
    (hs' : s' ∈ ipaths t) (hne : s ≠ s')
    (hpar : s.length % 2 = s'.length % 2) :
    Disjoint (star t s hs) (star t s' hs') := by
  by_contra h
  rcases star_not_disjoint_imp hs hs' h with h1 | h1 | h1
  · exact hne h1
  · have hne' : s' ≠ [] := by
      rintro rfl
      exact hne (by rw [h1]; rfl)
    have hlen := length_eq_dropLast_succ hne'
    rw [← h1] at hlen
    exact mod_two_ne_mod_two_succ s.length (by rw [hlen] at hpar; exact hpar)
  · have hsne : s ≠ [] := by
      rintro rfl
      exact hne (by rw [h1]; rfl)
    have hlen := length_eq_dropLast_succ hsne
    rw [← h1] at hlen
    exact mod_two_ne_mod_two_succ s'.length (by rw [hlen] at hpar; exact hpar.symm)

/-- Each 3-star has exactly three edges. -/
theorem card_star {t : RTree α} {s : List Bool} (hs : s ∈ ipaths t) :
    (star t s hs).card = 3 := by
  have hUp : ∀ b : Bool, (Sum.inl (⟨s, hs⟩, b) : AtlasEdge t) ≠ upEdge t s hs := by
    intro b hc
    obtain ⟨hne, hEq, -⟩ := upEdge_eq_downEdge hs hs hc.symm
    have hlen := length_eq_dropLast_succ hne
    rw [← hEq] at hlen
    omega
  have hBits : (Sum.inl (⟨s, hs⟩, false) : AtlasEdge t) ≠ Sum.inl (⟨s, hs⟩, true) := by
    intro hc
    have := (downEdge_inj hc).2
    simp at this
  have hb : (Sum.inl (⟨s, hs⟩, true) : AtlasEdge t) ∉
      ({upEdge t s hs} : Finset (AtlasEdge t)) := by
    simp [hUp true]
  have ha : (Sum.inl (⟨s, hs⟩, false) : AtlasEdge t) ∉
      (insert (Sum.inl (⟨s, hs⟩, true) : AtlasEdge t)
        ({upEdge t s hs} : Finset (AtlasEdge t))) := by
    simp [hBits, hUp false]
  simp only [star]
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
    Finset.card_singleton]

/-- **`#E = 2p - 1`:** the atlas of a tree with `p` leaves has `2 * #internal + 1` edges. -/
theorem card_atlasEdge (t : RTree α) :
    Fintype.card (AtlasEdge t) = 2 * (ipaths t).card + 1 := by
  have hsub : Fintype.card {s : List Bool // s ∈ ipaths t} = (ipaths t).card :=
    Fintype.card_of_subtype _ (fun x => Iff.rfl)
  change Fintype.card (({s : List Bool // s ∈ ipaths t} × Bool) ⊕ PUnit) =
    2 * (ipaths t).card + 1
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_punit, hsub]
  ring

/-- **The hub set uses exactly `3k` edges.**  If all hubs lie in one bipartition class then
the 3-stars are pairwise disjoint, so the number of atlas edges incident with the hub set is
`3 · #S`. -/
theorem card_hubEdges (t : RTree α) (S : Finset (List Bool)) (hS : S ⊆ ipaths t)
    (hpar : S ⊆ evenHubs t ∨ S ⊆ oddHubs t) :
    (hubEdges t S hS).card = 3 * S.card := by
  have hsame : ∀ a ∈ S, ∀ b ∈ S, a.length % 2 = b.length % 2 := by
    intro a ha b hb
    rcases hpar with h | h
    · have h1 : a.length % 2 = 0 := (Finset.mem_filter.mp (h ha)).2
      have h2 : b.length % 2 = 0 := (Finset.mem_filter.mp (h hb)).2
      omega
    · have h1 : a.length % 2 = 1 := (Finset.mem_filter.mp (h ha)).2
      have h2 : b.length % 2 = 1 := (Finset.mem_filter.mp (h hb)).2
      omega
  have hpd : (S.attach : Set {x // x ∈ S}).PairwiseDisjoint
      (fun p => star t p.1 (hS p.2)) := by
    intro a _ b _ hab
    exact star_disjoint (hS a.2) (hS b.2) (fun hc => hab (Subtype.ext hc)) (hsame a.1 a.2 b.1 b.2)
  rw [hubEdges, Finset.card_biUnion hpd]
  have h3 : ∀ p ∈ S.attach, (star t p.1 (hS p.2)).card = 3 := fun p _ => card_star (hS p.2)
  rw [Finset.sum_congr rfl h3, Finset.sum_const_nat (fun _ _ => rfl), Finset.card_attach]
  ring

/-- **The edges not incident with the hub set.**  Of the `2p - 1` atlas edges, exactly
`2p - 1 - 3k` are not adjacent to a vertex of the hub set of size `k`. -/
theorem card_edges_off_hubs (t : RTree α) (S : Finset (List Bool)) (hS : S ⊆ ipaths t)
    (hpar : S ⊆ evenHubs t ∨ S ⊆ oddHubs t) {k : ℕ} (hcard : S.card = k) :
    Fintype.card (AtlasEdge t) - (hubEdges t S hS).card = 2 * t.numLeaves - 1 - 3 * k := by
  rw [card_atlasEdge, card_hubEdges t S hS hpar, hcard, card_ipaths]
  have := numLeaves_pos t
  omega

/-- **The deselection step of Lemma I.4.16, packaged.**  For every atlas with `p` leaves and
every `k ≤ ⌈(p-1)/2⌉` there is a hub set of `k` internal vertices in one bipartition class;
the 3-stars at its vertices are pairwise disjoint and use exactly `3k` of the `2p - 1` atlas
edges, leaving `2p - 1 - 3k` edges that are not adjacent to the hub set. -/
theorem exists_hub_decomposition (t : RTree α) {k : ℕ}
    (hk : k ≤ (t.numLeaves - 1 + 1) / 2) :
    ∃ (S : Finset (List Bool)) (hS : S ⊆ ipaths t), S.card = k ∧
      (S ⊆ evenHubs t ∨ S ⊆ oddHubs t) ∧
      (hubEdges t S hS).card = 3 * k ∧
      Fintype.card (AtlasEdge t) = 2 * t.numLeaves - 1 ∧
      Fintype.card (AtlasEdge t) - (hubEdges t S hS).card = 2 * t.numLeaves - 1 - 3 * k := by
  obtain ⟨S, hS, hcard, hpar⟩ := exists_hubSet t hk
  have hpos := numLeaves_pos t
  refine ⟨S, hS, hcard, hpar, ?_, ?_, ?_⟩
  · rw [card_hubEdges t S hS hpar, hcard]
  · rw [card_atlasEdge, card_ipaths]
    omega
  · rw [card_edges_off_hubs t S hS hpar hcard]

/-! ### Non-vacuity: the instances `p = 3` and `p = 5` -/

/-- A concrete atlas with three leaves: `#internal = 2 = p - 1`, `#edges = 5 = 2p - 1`. -/
theorem check_three :
    (ipaths (node (leaf (0 : Fin 3)) (node (leaf 1) (leaf 2)))).card = 2 ∧
      Fintype.card (AtlasEdge (node (leaf (0 : Fin 3)) (node (leaf 1) (leaf 2)))) = 5 := by
  refine ⟨by decide, ?_⟩
  rw [card_atlasEdge]
  decide

/-- For the three-leaf atlas and `k = 1` (the case `p = 3`, `k = 1` of Lemma I.4.16, which
bounds `E|K|^3 ≤ 3 E|K|^2 (E|K|)^2`), the hub set exists and consumes `3` of the `5` edges,
leaving `2`. -/
theorem check_three_hub :
    ∃ (S : Finset (List Bool)) (hS : S ⊆ ipaths (node (leaf (0 : Fin 3)) (node (leaf 1) (leaf 2)))),
      S.card = 1 ∧ (hubEdges (node (leaf (0 : Fin 3)) (node (leaf 1) (leaf 2))) S hS).card = 3 ∧
      Fintype.card (AtlasEdge (node (leaf (0 : Fin 3)) (node (leaf 1) (leaf 2)))) -
        (hubEdges (node (leaf (0 : Fin 3)) (node (leaf 1) (leaf 2))) S hS).card = 2 := by
  obtain ⟨S, hS, hc, hp, h1, h2, h3⟩ :=
    exists_hub_decomposition (node (leaf (0 : Fin 3)) (node (leaf 1) (leaf 2))) (k := 1)
      (by decide)
  refine ⟨S, hS, hc, ?_, ?_⟩
  · rw [h1]
  · rw [h3]
    decide

/-- A concrete atlas with five leaves: `#internal = 4`, `#edges = 9 = 2·5 - 1`. -/
theorem check_five :
    (ipaths (node (node (leaf (0 : Fin 5)) (leaf 1))
      (node (leaf 2) (node (leaf 3) (leaf 4))))).card = 4 ∧
      Fintype.card (AtlasEdge (node (node (leaf (0 : Fin 5)) (leaf 1))
        (node (leaf 2) (node (leaf 3) (leaf 4))))) = 9 := by
  refine ⟨by decide, ?_⟩
  rw [card_atlasEdge]
  decide

/-- For the five-leaf atlas and `k = 2` (the case `p = 5`, `k = 2` of Lemma I.4.16), the hub
set consumes `6` of the `9` edges, leaving `3`. -/
theorem check_five_hub :
    ∃ (S : Finset (List Bool))
      (hS : S ⊆ ipaths (node (node (leaf (0 : Fin 5)) (leaf 1))
        (node (leaf 2) (node (leaf 3) (leaf 4))))),
      S.card = 2 ∧
      (hubEdges (node (node (leaf (0 : Fin 5)) (leaf 1))
        (node (leaf 2) (node (leaf 3) (leaf 4)))) S hS).card = 6 ∧
      Fintype.card (AtlasEdge (node (node (leaf (0 : Fin 5)) (leaf 1))
        (node (leaf 2) (node (leaf 3) (leaf 4))))) -
        (hubEdges (node (node (leaf (0 : Fin 5)) (leaf 1))
          (node (leaf 2) (node (leaf 3) (leaf 4)))) S hS).card = 3 := by
  obtain ⟨S, hS, hc, hp, h1, h2, h3⟩ :=
    exists_hub_decomposition (node (node (leaf (0 : Fin 5)) (leaf 1))
      (node (leaf 2) (node (leaf 3) (leaf 4)))) (k := 2) (by decide)
  refine ⟨S, hS, hc, ?_, ?_⟩
  · rw [h1]
  · rw [h3]
    decide

/-! ### The three arms at a hub -/

/-- Every tree has at least one leaf. -/
theorem lpaths_nonempty (t : RTree α) : (lpaths t).Nonempty := by
  induction t with
  | leaf a => exact ⟨[], by simp [lpaths]⟩
  | node l r ihl ihr =>
      obtain ⟨u, hu⟩ := ihl
      exact ⟨false :: u, by simp [lpaths, hu]⟩

/-- A leaf below an internal address: the leaves of the subtree at `p`, shifted to `p`. -/
theorem mem_image_lpaths_of_subAt {t T : RTree α} {p : List Bool} (hp : subAt t p = some T)
    {u : List Bool} (hu : u ∈ lpaths T) : p ++ u ∈ lpaths t := by
  obtain ⟨a, ha⟩ := (mem_lpaths T u).mp hu
  refine (mem_lpaths t (p ++ u)).mpr ⟨a, ?_⟩
  rw [subAt_append, hp]
  exact ha

/-- **The three arms of a hub.**  At an internal vertex `v` of the atlas with children
`l` and `r`, the leaves of the tree split into the leaves below `l`, the leaves below `r`,
and the remaining leaves — the third, "upward" arm, which in the atlas also contains the
root leaf `0`.  The two downward arms are nonempty with pairwise disjoint leaf sets, and the
three parts cover all leaves.  This is the deterministic input to the three-fold BK step at
a hub in the proof of Lemma I.4.16. -/
theorem leaf_arms {t : RTree α} {v : List Bool} (hv : v ∈ ipaths t) :
    ∃ (l r : RTree α) (L R U : Finset (List Bool)),
      subAt t v = some (node l r) ∧
      L = (lpaths l).image (fun u => (v ++ [false]) ++ u) ∧
      R = (lpaths r).image (fun u => (v ++ [true]) ++ u) ∧
      U = lpaths t \ (L ∪ R) ∧
      L.Nonempty ∧ R.Nonempty ∧
      Disjoint L R ∧ Disjoint L U ∧ Disjoint R U ∧
      L ∪ R ∪ U = lpaths t := by
  obtain ⟨l, r, hl⟩ := (mem_ipaths t v).mp hv
  have hfl : subAt t (v ++ [false]) = some l := by
    rw [subAt_append, hl]
    simp
  have hfr : subAt t (v ++ [true]) = some r := by
    rw [subAt_append, hl]
    simp
  set L : Finset (List Bool) := (lpaths l).image (fun u => (v ++ [false]) ++ u) with hL
  set R : Finset (List Bool) := (lpaths r).image (fun u => (v ++ [true]) ++ u) with hR
  refine ⟨l, r, L, R, lpaths t \ (L ∪ R), hl, hL, hR, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := lpaths_nonempty l
    exact ⟨_, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
  · obtain ⟨u, hu⟩ := lpaths_nonempty r
    exact ⟨_, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
  · refine Finset.disjoint_left.mpr fun s hs hsr => ?_
    rw [hL] at hs
    rw [hR] at hsr
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨u', _, hu'⟩ := Finset.mem_image.mp hsr
    have h3 := congrArg (fun x => x.drop v.length) hu'
    simp only [List.append_assoc, List.singleton_append, List.drop_left] at h3
    have h4 := (List.cons.inj h3).1
    simp at h4
  · refine Finset.disjoint_left.mpr fun s hsL hsU => ?_
    rw [Finset.mem_sdiff] at hsU
    exact hsU.2 (Finset.mem_union_left _ hsL)
  · refine Finset.disjoint_left.mpr fun s hsR hsU => ?_
    rw [Finset.mem_sdiff] at hsU
    exact hsU.2 (Finset.mem_union_right _ hsR)
  · refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · rw [hL] at hx
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
          exact mem_image_lpaths_of_subAt hfl hu
        · rw [hR] at hx
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
          exact mem_image_lpaths_of_subAt hfr hu
      · rw [Finset.mem_sdiff] at hx
        exact hx.1
    · intro x hx
      rw [Finset.mem_union]
      by_cases h : x ∈ L ∪ R
      · exact Or.inl h
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨hx, h⟩)

end RTree

end PercLib.CriticalLRP.TreeExpansion
