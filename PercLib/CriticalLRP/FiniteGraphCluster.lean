/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Clusters of a finite graph and the effect of flipping one edge, for
Hutchcroft, "Critical long-range percolation I", arXiv:2508.18807v1,
Lemma I.4.1.

The proof of Lemma I.4.1 uses, for an edge `e = {x,y}`, that opening `e` in a
configuration in which `x` lies in the cluster `K` of the origin and `y` does
not, merges the cluster of `x` (= `K`) with the cluster of `y` and changes
nothing else, whereas opening an edge with both endpoints inside `K` or both
outside `K` leaves `K` unchanged. This file proves exactly that, for a finite
(multi)graph given by an edge type `E` with endpoint maps `s, t : E → V`, so
that it applies to the cut-off graphs of Section I.4.

Everything is finite and combinatorial; no probability enters.
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Pi
public import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.FiniteVolume

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
/-- The adjacency relation of the open subgraph of the edge set `ω`. -/
def step (s t : E → V) (ω : Finset E) (u v : V) : Prop :=
  ∃ e ∈ ω, (s e = u ∧ t e = v) ∨ (s e = v ∧ t e = u)

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem step_comm {s t : E → V} {ω : Finset E} {u v : V} (h : step s t ω u v) :
    step s t ω v u := by
  obtain ⟨e, he, h1 | h1⟩ := h
  · exact ⟨e, he, Or.inr h1⟩
  · exact ⟨e, he, Or.inl h1⟩

/-- Connectivity in the open subgraph. -/
def Conn (s t : E → V) (ω : Finset E) (u v : V) : Prop :=
  Relation.ReflTransGen (step s t ω) u v

theorem conn_refl (s t : E → V) (ω : Finset E) (u : V) : Conn s t ω u u :=
  Relation.ReflTransGen.refl

theorem conn_trans {s t : E → V} {ω : Finset E} {u v w : V}
    (h1 : Conn s t ω u v) (h2 : Conn s t ω v w) : Conn s t ω u w := h1.trans h2

theorem conn_symm {s t : E → V} {ω : Finset E} {u v : V} (h : Conn s t ω u v) :
    Conn s t ω v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact (Relation.ReflTransGen.single (step_comm hbc)).trans ih

theorem conn_mono {s t : E → V} {ω ω' : Finset E} (h : ω ⊆ ω') {u v : V}
    (hc : Conn s t ω u v) : Conn s t ω' u v := by
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      refine ih.trans (Relation.ReflTransGen.single ?_)
      obtain ⟨e, he, hst⟩ := hbc
      exact ⟨e, h he, hst⟩

theorem step_insert {s t : E → V} (e : E) (ω : Finset E) (u v : V) :
    step s t (insert e ω) u v ↔
      step s t ω u v ∨ (s e = u ∧ t e = v) ∨ (s e = v ∧ t e = u) := by
  unfold step
  constructor
  · rintro ⟨e', he', hst⟩
    rw [mem_insert] at he'
    rcases he' with rfl | he'
    · exact Or.inr hst
    · exact Or.inl ⟨e', he', hst⟩
  · rintro (⟨e', he', hst⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨e', mem_insert_of_mem he', hst⟩
    · exact ⟨e, mem_insert_self e ω, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨e, mem_insert_self e ω, Or.inr ⟨h1, h2⟩⟩

/-- **Adding one edge**: two vertices are connected in `ω ∪ {e}` iff they were
connected in `ω`, or one is connected to an endpoint of `e` and the other to the
other endpoint. -/
theorem conn_insert_iff {s t : E → V} (e : E) (ω : Finset E) (u v : V) :
    Conn s t (insert e ω) u v ↔
      Conn s t ω u v ∨ (Conn s t ω u (s e) ∧ Conn s t ω (t e) v)
        ∨ (Conn s t ω u (t e) ∧ Conn s t ω (s e) v) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl Relation.ReflTransGen.refl
    | tail _ hbc ih =>
        rw [step_insert] at hbc
        rcases hbc with hold | hstep | hstep
        · rcases ih with h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl (h0.tail hold)
          · exact Or.inr (Or.inl ⟨ha, hb.tail hold⟩)
          · exact Or.inr (Or.inr ⟨ha, hb.tail hold⟩)
        · obtain ⟨h1, h2⟩ := hstep
          subst h1 h2
          rcases ih with h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inr (Or.inl ⟨h0, Relation.ReflTransGen.refl⟩)
          · exact Or.inl (ha.trans (conn_symm hb))
          · exact Or.inl ha
        · obtain ⟨h1, h2⟩ := hstep
          subst h1 h2
          rcases ih with h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inr (Or.inr ⟨h0, Relation.ReflTransGen.refl⟩)
          · exact Or.inl ha
          · exact Or.inl (ha.trans (conn_symm hb))
  · rintro (h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact conn_mono (subset_insert e ω) h0
    · refine (conn_mono (subset_insert e ω) ha).trans ?_
      exact (Relation.ReflTransGen.single
        ⟨e, mem_insert_self e ω, Or.inl ⟨rfl, rfl⟩⟩).trans
        (conn_mono (subset_insert e ω) hb)
    · refine (conn_mono (subset_insert e ω) ha).trans ?_
      exact (Relation.ReflTransGen.single
        ⟨e, mem_insert_self e ω, Or.inr ⟨rfl, rfl⟩⟩).trans
        (conn_mono (subset_insert e ω) hb)

/-- The cluster of `u`: the set of vertices connected to `u`. -/
noncomputable def cluster (s t : E → V) (ω : Finset E) (u : V) : Finset V := by
  classical
  exact univ.filter (fun v => Conn s t ω u v)

theorem mem_cluster {s t : E → V} {ω : Finset E} {u v : V} :
    v ∈ cluster s t ω u ↔ Conn s t ω u v := by
  classical
  unfold cluster
  simp

theorem self_mem_cluster (s t : E → V) (ω : Finset E) (u : V) :
    u ∈ cluster s t ω u := by
  classical
  rw [mem_cluster]; exact conn_refl s t ω u

theorem cluster_eq_of_conn {s t : E → V} {ω : Finset E} {u v : V}
    (h : Conn s t ω u v) : cluster s t ω u = cluster s t ω v := by
  classical
  ext w
  rw [mem_cluster, mem_cluster]
  exact ⟨fun hw => (conn_symm h).trans hw, fun hw => h.trans hw⟩

/-! ### Flipping an edge that joins `x` to the complement of its cluster -/

/-- If `t e` is not connected to `s e`, then opening `e` adds exactly the
cluster of `t e` to the cluster of `s e`. -/
theorem mem_cluster_insert_of_not_conn {s t : E → V} {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) (w : V) :
    w ∈ cluster s t (insert e ω) (s e) ↔
      w ∈ cluster s t ω (s e) ∨ w ∈ cluster s t ω (t e) := by
  classical
  rw [mem_cluster, mem_cluster, mem_cluster, conn_insert_iff]
  constructor
  · rintro (h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact Or.inl h0
    · exact Or.inr hb
    · exact Or.inl hb
  · rintro (h0 | h0)
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨conn_refl s t ω (s e), h0⟩)

/-- The same statement based at `t e`. -/
theorem mem_cluster_insert_right {s t : E → V} {e : E} {ω : Finset E} (w : V) :
    w ∈ cluster s t (insert e ω) (t e) ↔
      w ∈ cluster s t ω (t e) ∨ w ∈ cluster s t ω (s e) := by
  classical
  rw [mem_cluster, mem_cluster, mem_cluster, conn_insert_iff]
  constructor
  · rintro (h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact Or.inl h0
    · exact Or.inl hb
    · exact Or.inr hb
  · rintro (h0 | h0)
    · exact Or.inl h0
    · exact Or.inr (Or.inr ⟨conn_refl s t ω (t e), h0⟩)

/-- The two clusters merged by opening `e` are disjoint when `t e` is not
connected to `s e`. -/
theorem disjoint_cluster_of_not_conn {s t : E → V} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    Disjoint (cluster s t ω (s e)) (cluster s t ω (t e)) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwx hwy
  rw [mem_cluster] at hwx hwy
  exact absurd (hwx.trans (conn_symm hwy)) hxy

/-- **Cluster size after opening a merging edge**: the new cluster size is the
sum of the two old cluster sizes. -/
theorem card_cluster_insert_of_not_conn {s t : E → V} {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    (cluster s t (insert e ω) (s e)).card
      = (cluster s t ω (s e)).card + (cluster s t ω (t e)).card := by
  classical
  have hunion : cluster s t (insert e ω) (s e)
      = cluster s t ω (s e) ∪ cluster s t ω (t e) := by
    ext w
    rw [mem_cluster_insert_of_not_conn hxy, mem_union]
  rw [hunion, card_union_of_disjoint (disjoint_cluster_of_not_conn hxy)]

/-- Cluster size after opening a merging edge, based at `t e`. -/
theorem card_cluster_insert_right {s t : E → V} {e : E} {ω : Finset E}
    (hxy : ¬ Conn s t ω (s e) (t e)) :
    (cluster s t (insert e ω) (t e)).card
      = (cluster s t ω (t e)).card + (cluster s t ω (s e)).card := by
  classical
  have hunion : cluster s t (insert e ω) (t e)
      = cluster s t ω (t e) ∪ cluster s t ω (s e) := by
    ext w
    rw [mem_cluster_insert_right, mem_union]
  rw [hunion, card_union_of_disjoint
    (disjoint_comm.mpr (disjoint_cluster_of_not_conn hxy))]

/-! ### Flipping an edge whose endpoints are already connected -/

/-- If the endpoints of `e` are already connected, opening `e` changes no
cluster. -/
theorem cluster_insert_of_conn {s t : E → V} {e : E} {ω : Finset E}
    (hxy : Conn s t ω (s e) (t e)) (u : V) :
    cluster s t (insert e ω) u = cluster s t ω u := by
  classical
  ext w
  rw [mem_cluster, mem_cluster, conn_insert_iff]
  constructor
  · rintro (h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact h0
    · exact ha.trans (hxy.trans hb)
    · exact ha.trans ((conn_symm hxy).trans hb)
  · exact fun h0 => Or.inl h0

/-- If `u` is connected to neither endpoint of `e`, opening `e` changes the
cluster of `u` not at all. -/
theorem cluster_insert_of_not_conn_both {s t : E → V} {e : E} {ω : Finset E} {u : V}
    (h1 : ¬ Conn s t ω u (s e)) (h2 : ¬ Conn s t ω u (t e)) :
    cluster s t (insert e ω) u = cluster s t ω u := by
  classical
  ext w
  rw [mem_cluster, mem_cluster, conn_insert_iff]
  constructor
  · rintro (h0 | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact h0
    · exact absurd ha h1
    · exact absurd ha h2
  · exact fun h0 => Or.inl h0

end Graph

end PercLib.CriticalLRP.FiniteVolume
