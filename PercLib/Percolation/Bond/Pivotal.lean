/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 199, Q-38). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.LocalConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Pivotal pairs for connection events

A pair `e` is pivotal for `x ↔ y` in `ω` when `insert e ω ∈ conn x y` and
`ω \ {e} ∉ conn x y` (the spelling of `Russo.lean`; no pivotal definition is introduced).

* `e = s(a, b)` with `a ≠ b` is pivotal exactly when, with `e` closed, `x` and `y` are not
  joined but one is joined to `a` and the other to `b`.
* Diagonal pairs are never pivotal.
* A pivotal pair lies on every open walk from `x` to `y`; so there are at most
  `dist(x, y)` pivotal pairs.
* Pairs not internal to a domain are never pivotal for its internal connection events.
-/

@[expose] public section

noncomputable section

open Set

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Adding one pair -/

/-- A connection that appears when one pair is added runs through that pair. -/
theorem reachable_sdiff_or_of_reachable_insert {ω : Config V} {a b x y : V}
    (h : (openGraph (insert s(a, b) ω)).Reachable x y) :
    (openGraph (ω \ {s(a, b)})).Reachable x y ∨
      ((openGraph (ω \ {s(a, b)})).Reachable x a ∧ (openGraph (ω \ {s(a, b)})).Reachable b y) ∨
      ((openGraph (ω \ {s(a, b)})).Reachable x b ∧ (openGraph (ω \ {s(a, b)})).Reachable a y) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @cons u z v huz p ih =>
    set G0 := openGraph (ω \ {s(a, b)})
    rw [openGraph_adj_iff, mem_insert_iff] at huz
    by_cases he : s(u, z) = s(a, b)
    · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- `u = a`, `z = b`
        rcases ih with h | ⟨h1, h2⟩ | ⟨-, h2⟩
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h⟩)
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h2⟩)
        · exact Or.inl h2
      · -- `u = b`, `z = a`
        rcases ih with h | ⟨-, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h⟩)
        · exact Or.inl h2
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h2⟩)
    · have hadj : G0.Adj u z := by
        rw [openGraph_adj_iff]
        exact ⟨⟨huz.1.resolve_left he, he⟩, huz.2⟩
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (hadj.reachable.trans h)
      · exact Or.inr (Or.inl ⟨hadj.reachable.trans h1, h2⟩)
      · exact Or.inr (Or.inr ⟨hadj.reachable.trans h1, h2⟩)

/-- **Characterisation of pivotal pairs.** -/
theorem pivotal_conn_iff (ω : Config V) (x y a b : V) (hab : a ≠ b) :
    (insert s(a, b) ω ∈ conn x y ∧ ω \ {s(a, b)} ∉ conn x y) ↔
      ω \ {s(a, b)} ∉ conn x y ∧
        ((ω \ {s(a, b)} ∈ conn x a ∧ ω \ {s(a, b)} ∈ conn y b) ∨
          (ω \ {s(a, b)} ∈ conn x b ∧ ω \ {s(a, b)} ∈ conn y a)) := by
  have hsub : ω \ {s(a, b)} ⊆ insert s(a, b) ω := fun e he => mem_insert_of_mem _ he.1
  have hedge : insert s(a, b) ω ∈ conn a b := mem_conn_of_mem hab (mem_insert _ _)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rcases reachable_sdiff_or_of_reachable_insert h1 with h | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact absurd h h2
    · exact Or.inl ⟨h3, h4.symm⟩
    · exact Or.inr ⟨h3, h4.symm⟩
  · rintro ⟨h2, h | h⟩
    · refine ⟨?_, h2⟩
      exact conn_trans (conn_trans (conn_mono hsub h.1) hedge)
        ((conn_symm y b ▸ conn_mono hsub h.2 : insert s(a, b) ω ∈ conn b y))
    · refine ⟨?_, h2⟩
      have hedge' : insert s(a, b) ω ∈ conn b a := conn_symm a b ▸ hedge
      exact conn_trans (conn_trans (conn_mono hsub h.1) hedge')
        ((conn_symm y a ▸ conn_mono hsub h.2 : insert s(a, b) ω ∈ conn a y))

/-! ### Diagonal pairs -/

/-- **Diagonal pairs are never pivotal.** -/
theorem not_pivotal_conn_of_isDiag (ω : Config V) (x y : V) {e : Sym2 V} (he : e.IsDiag) :
    ¬ (insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y) := by
  rintro ⟨h1, h2⟩
  have hg : openGraph (insert e ω) = openGraph (ω \ {e}) := by
    ext u v
    simp only [openGraph_adj_iff, mem_insert_iff, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨h | h, huv⟩
      · exact absurd (h ▸ he) (Sym2.mk_isDiag_iff.not.2 huv)
      · exact ⟨⟨h, fun h' => (Sym2.mk_isDiag_iff.not.2 huv) (h' ▸ he)⟩, huv⟩
    · rintro ⟨⟨h, -⟩, huv⟩
      exact ⟨Or.inr h, huv⟩
  exact h2 (by rw [mem_conn_iff, ← hg]; exact h1)

/-! ### Pivotal pairs lie on every path -/

/-- **A pivotal pair lies on every open walk** from `x` to `y`. -/
theorem mem_edges_of_pivotal {ω : Config V} {x y : V} {e : Sym2 V}
    (hpiv : ω \ {e} ∉ conn x y) (w : (openGraph ω).Walk x y) : e ∈ w.edges := by
  by_contra hnot
  refine hpiv ⟨w.transfer (openGraph (ω \ {e})) fun f hf => ?_⟩
  have h1 := w.edges_subset_edgeSet hf
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1 ⊢
  exact ⟨⟨h1.1, fun h => hnot (mem_singleton_iff.1 h ▸ hf)⟩, h1.2⟩

/-- A pair pivotal for a realised connection is open. -/
theorem mem_of_pivotal {ω : Config V} {x y : V} {e : Sym2 V} (hω : ω ∈ conn x y)
    (hpiv : ω \ {e} ∉ conn x y) : e ∈ ω := by
  obtain ⟨w⟩ := hω
  have h1 := w.edges_subset_edgeSet (mem_edges_of_pivotal hpiv w)
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1
  exact h1.1

/-- **Counting.** There are at most `dist(x, y)` pairs pivotal for a realised connection. -/
theorem encard_pivotal_le_dist {ω : Config V} {x y : V} (hω : ω ∈ conn x y) :
    {e : Sym2 V | insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y}.encard ≤
      (openGraph ω).dist x y := by
  classical
  obtain ⟨w, hw⟩ := (hω : (openGraph ω).Reachable x y).exists_walk_length_eq_dist
  calc {e : Sym2 V | insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y}.encard
      ≤ ((w.edges.toFinset : Finset (Sym2 V)) : Set (Sym2 V)).encard :=
        Set.encard_le_encard fun e he => by
          simpa using mem_edges_of_pivotal he.2 w
    _ = w.edges.toFinset.card := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ w.edges.length := by exact_mod_cast List.toFinset_card_le _
    _ = (openGraph ω).dist x y := by rw [SimpleGraph.Walk.length_edges, hw]

/-! ### Internal connection events -/

/-- **Pairs not internal to a domain are never pivotal** for its internal connection events. -/
theorem not_pivotal_localConn_of_not_internal (ω : Config V) (S : Set V) (x y : S)
    {e : Sym2 V} (he : ¬ ∀ v ∈ e, v ∈ S) :
    ¬ (((openGraph (insert e ω)).induce S).Reachable x y ∧
        ¬ ((openGraph (ω \ {e})).induce S).Reachable x y) := by
  rintro ⟨h1, h2⟩
  refine h2 ((localConn_iff_of_agree S x y fun a ha b hb => ?_).1 h1)
  have hne : s(a, b) ≠ e := by
    rintro rfl
    refine he fun v hv => ?_
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ha
    · exact hb
  simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff, hne, false_or, not_false_eq_true,
    and_true]

/-- Pulling back along the inclusion of a domain commutes with adding and removing an internal
pair. -/
theorem preimage_sym2Map_val_insert (ω : Config V) (S : Set V) (a b : S) :
    (Sym2.map (Subtype.val : S → V) ⁻¹' insert s((a : V), (b : V)) ω) =
      insert s(a, b) (Sym2.map (Subtype.val : S → V) ⁻¹' ω) := by
  ext e
  simp only [mem_preimage, mem_insert_iff]
  rw [show s((a : V), (b : V)) = Sym2.map Subtype.val s(a, b) from rfl,
    (Sym2.map.injective Subtype.val_injective).eq_iff]

theorem preimage_sym2Map_val_sdiff (ω : Config V) (S : Set V) (a b : S) :
    (Sym2.map (Subtype.val : S → V) ⁻¹' (ω \ {s((a : V), (b : V))})) =
      (Sym2.map (Subtype.val : S → V) ⁻¹' ω) \ {s(a, b)} := by
  ext e
  simp only [mem_preimage, mem_sdiff, mem_singleton_iff]
  rw [show s((a : V), (b : V)) = Sym2.map Subtype.val s(a, b) from rfl,
    (Sym2.map.injective Subtype.val_injective).eq_iff]

/-- **Internal version of the characterisation.** For a pair internal to `S`, pivotality for
an internal connection of `S` is the characterisation of `pivotal_conn_iff` inside `S`. -/
theorem pivotal_localConn_iff (ω : Config V) (S : Set V) (x y a b : S) (hab : a ≠ b) :
    (((openGraph (insert s((a : V), (b : V)) ω)).induce S).Reachable x y ∧
        ¬ ((openGraph (ω \ {s((a : V), (b : V))})).induce S).Reachable x y) ↔
      ¬ ((openGraph (ω \ {s((a : V), (b : V))})).induce S).Reachable x y ∧
        ((((openGraph (ω \ {s((a : V), (b : V))})).induce S).Reachable x a ∧
            ((openGraph (ω \ {s((a : V), (b : V))})).induce S).Reachable y b) ∨
          (((openGraph (ω \ {s((a : V), (b : V))})).induce S).Reachable x b ∧
            ((openGraph (ω \ {s((a : V), (b : V))})).induce S).Reachable y a)) := by
  simp only [openGraph_induce, preimage_sym2Map_val_insert, preimage_sym2Map_val_sdiff]
  exact pivotal_conn_iff _ x y a b hab

/-! ### Non-vacuity -/

/-- Nothing is pivotal for `x ↔ x`. -/
example (ω : Config V) (x : V) (e : Sym2 V) : ¬ (insert e ω ∈ conn x x ∧ ω \ {e} ∉ conn x x) :=
  fun h => h.2 (SimpleGraph.Reachable.refl x)

/-- With no open pair, the pair `s(0, 1)` of `Fin 2` is pivotal for `0 ↔ 1`. -/
example : insert s((0 : Fin 2), 1) (∅ : Config (Fin 2)) ∈ conn 0 1 ∧
    (∅ : Config (Fin 2)) \ {s(0, 1)} ∉ conn 0 1 := by
  refine (pivotal_conn_iff ∅ 0 1 0 1 (by decide)).2 ⟨?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [empty_sdiff, empty_mem_conn_iff]
    decide
  · rw [empty_sdiff]
    exact SimpleGraph.Reachable.refl _
  · rw [empty_sdiff]
    exact SimpleGraph.Reachable.refl _

end PercLib.Percolation.Bond

end
