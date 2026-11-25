/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 223, Q-47). No upstream proof is copied.
-/
module

public import PercLib.Probability.OpenEventHarris

/-!
# Closed certificates for non-connection

The edge boundary of the cluster of `x` is closed, and `x` is not connected to `y` exactly
when some set of vertices containing `x` but not `y` has a closed edge boundary (the cluster of
`x` being the canonical one), equivalently when some closed set of pairs separates `x` from
`y`. These are the witnesses of decreasing connection events. Deterministic; no countability.
-/

@[expose] public section

noncomputable section

open Set

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The boundary of a cluster is closed -/

/-- **Cluster boundary.** No pair from the cluster of `x` to its complement is open. -/
theorem notMem_of_mem_cluster_of_notMem (ω : Config V) {x a b : V} (ha : a ∈ cluster ω x)
    (hb : b ∉ cluster ω x) : s(a, b) ∉ ω := by
  intro h
  have hab : a ≠ b := fun h' => hb (h' ▸ ha)
  exact hb (conn_trans ha (mem_conn_of_mem hab h))

/-- A set with closed edge boundary contains everything connected to its points. -/
theorem mem_of_mem_conn_of_closed {ω : Config V} {C : Set V}
    (hC : ∀ a ∈ C, ∀ b ∉ C, s(a, b) ∉ ω) {u v : V} (h : ω ∈ conn u v) (hu : u ∈ C) :
    v ∈ C := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | @cons a b c hab p ih =>
    refine ih ?_
    by_contra hb
    exact hC a hu b hb ((openGraph_adj_iff ω a b).1 hab).1

/-- **Characterisation.** `x` is not connected to `y` iff some set containing `x` but not `y`
has a closed edge boundary; the cluster of `x` is a witness. -/
theorem not_mem_conn_iff_exists_closed_separating (ω : Config V) (x y : V) :
    ω ∉ conn x y ↔ ∃ C : Set V, x ∈ C ∧ y ∉ C ∧ ∀ a ∈ C, ∀ b ∉ C, s(a, b) ∉ ω := by
  constructor
  · intro h
    exact ⟨cluster ω x, mem_cluster_self ω x, h, fun a ha b hb =>
      notMem_of_mem_cluster_of_notMem ω ha hb⟩
  · rintro ⟨C, hx, hy, hC⟩ h
    exact hy (mem_of_mem_conn_of_closed hC h hx)

/-- **Finite certificates.** If the cluster of `x` is finite and does not reach `y`, the witness
can be taken to be a finite set. -/
theorem exists_finset_closed_separating {ω : Config V} {x y : V}
    (hfin : (cluster ω x).Finite) (h : ω ∉ conn x y) :
    ∃ C : Finset V, x ∈ C ∧ y ∉ C ∧ ∀ a ∈ C, ∀ b ∉ C, s(a, b) ∉ ω :=
  ⟨hfin.toFinset, hfin.mem_toFinset.2 (mem_cluster_self ω x),
    fun hy => h (hfin.mem_toFinset.1 hy), fun _ ha _ hb =>
      notMem_of_mem_cluster_of_notMem ω (hfin.mem_toFinset.1 ha)
        fun h' => hb (hfin.mem_toFinset.2 h')⟩

/-! ### Separating sets of pairs -/

/-- A walk from inside a set to outside it uses a pair of the edge boundary. -/
theorem exists_mem_edges_boundary {G : SimpleGraph V} {C : Set V} {u v : V} (w : G.Walk u v)
    (hu : u ∈ C) (hv : v ∉ C) : ∃ a ∈ C, ∃ b ∉ C, s(a, b) ∈ w.edges := by
  induction w with
  | nil => exact absurd hu hv
  | @cons a b c hab p ih =>
    by_cases hb : b ∈ C
    · obtain ⟨a', ha', b', hb', he⟩ := ih hb hv
      exact ⟨a', ha', b', hb', by simp [he]⟩
    · exact ⟨a, hu, b, hb, by simp⟩

/-- **Characterisation by separating pairs.** `x` is not connected to `y` iff some closed set of
pairs meets every walk from `x` to `y` in the complete graph; the edge boundary of the cluster
of `x` is a witness. -/
theorem not_mem_conn_iff_exists_closed_separating_pairs (ω : Config V) (x y : V) :
    ω ∉ conn x y ↔ ∃ P : Set (Sym2 V),
      (∀ w : (⊤ : SimpleGraph V).Walk x y, ∃ e ∈ w.edges, e ∈ P) ∧ Disjoint P ω := by
  constructor
  · intro h
    refine ⟨{e | ∃ a ∈ cluster ω x, ∃ b ∉ cluster ω x, e = s(a, b)}, fun w => ?_, ?_⟩
    · obtain ⟨a, ha, b, hb, he⟩ := exists_mem_edges_boundary w (mem_cluster_self ω x) h
      exact ⟨s(a, b), he, a, ha, b, hb, rfl⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact notMem_of_mem_cluster_of_notMem ω ha hb
  · rintro ⟨P, hP, hdisj⟩ ⟨w⟩
    have hedges : ∀ e ∈ w.edges, e ∈ (⊤ : SimpleGraph V).edgeSet := by
      intro e he
      have h1 := w.edges_subset_edgeSet he
      rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1
      rw [SimpleGraph.edgeSet_top]
      exact h1.2
    obtain ⟨e, he, heP⟩ := hP (w.transfer ⊤ hedges)
    rw [SimpleGraph.Walk.edges_transfer] at he
    have h1 := w.edges_subset_edgeSet he
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1
    exact Set.disjoint_left.1 hdisj heP h1.1

/-! ### Decreasing events -/

/-- Non-connection is a decreasing event. (The same statement is `isLowerSet_compl_conn` in
#149; this copy has its own name so that both pull requests build.) -/
theorem isLowerSet_conn_compl (x y : V) : IsLowerSet ((conn x y)ᶜ : Set (Config V)) :=
  (isUpperSet_conn x y).compl

/-- Finiteness of a cluster is a decreasing event. -/
theorem isLowerSet_cluster_finite (x : V) :
    IsLowerSet {ω : Config V | (cluster ω x).Finite} := fun _ _ hle hfin =>
  hfin.subset (cluster_mono hle x)

/-- For `x ∈ C`, the cluster of `x` lies in `C` exactly when no pair from the cluster to the
complement of `C` is open. -/
theorem cluster_subset_iff (ω : Config V) {x : V} {C : Set V} (hx : x ∈ C) :
    cluster ω x ⊆ C ↔ ∀ a ∈ cluster ω x, ∀ b ∉ C, s(a, b) ∉ ω := by
  constructor
  · intro hsub a ha b hb
    exact notMem_of_mem_cluster_of_notMem ω ha fun h => hb (hsub h)
  · intro h y hy
    obtain ⟨w⟩ := hy
    suffices ∀ {u v : V} (w : (openGraph ω).Walk u v), u ∈ C → u ∈ cluster ω x → v ∈ C from
      this w hx (mem_cluster_self ω x)
    intro u v w
    induction w with
    | nil => exact fun hu _ => hu
    | @cons a b c hab p ih =>
      intro ha hax
      have hbx : b ∈ cluster ω x := conn_trans hax hab.reachable
      refine ih ?_ hbx
      by_contra hb
      exact h a hax b hb ((openGraph_adj_iff ω a b).1 hab).1

/-! ### Non-vacuity -/

/-- With no open pair, `{x}` certifies that `x` is connected to no other vertex. -/
example (x y : V) (hxy : x ≠ y) : (∅ : Config V) ∉ conn x y :=
  (not_mem_conn_iff_exists_closed_separating ∅ x y).2
    ⟨{x}, rfl, fun h => hxy (h.symm), fun _ _ _ _ h => h⟩

/-- With every pair open on two points, there is no closed separating set. -/
example : ¬ ∃ C : Set Bool, false ∈ C ∧ true ∉ C ∧
    ∀ a ∈ C, ∀ b ∉ C, s(a, b) ∉ (Set.univ : Config Bool) := by
  rw [← not_mem_conn_iff_exists_closed_separating, not_not]
  exact mem_conn_of_mem (by decide) (Set.mem_univ _)

end PercLib.Percolation.Bond

end
