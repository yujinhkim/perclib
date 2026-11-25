/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The cluster of `o` equals a finite set: description by the edges meeting that set

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.12 (p. 39).  The rewiring set there is the set of edges
touching `K_0`, and the argument needs the standard fact that **the event `{K_0 = A}` is decided
by the states of the edges meeting `A`** (for finite `A`), so that the configuration away from `A`
is an independent fresh copy.

This file proves the deterministic description behind that fact:

  `cluster ω o = ↑A ↔ o ∈ A ∧ (∀ a ∈ A, Connects (ω ∩ inside A) o a)
      ∧ (∀ e ∈ touchOf A, e ∉ inside A → e ∉ ω)`

where `inside A` is the set of edges with both endpoints in `A` and `touchOf A` is the set of edges
with at least one endpoint in `A`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.ClusterWindow

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The edges with both endpoints in `A`. -/
def inside (A : Finset V) : Set (Sym2 V) := {e | ∀ v ∈ e, v ∈ (A : Set V)}

/-- The edges with at least one endpoint in `A`. -/
def touchOf (A : Finset V) : Set (Sym2 V) := {e | ∃ v ∈ (A : Set V), v ∈ e}

theorem mem_inside {A : Finset V} {e : Sym2 V} :
    e ∈ inside A ↔ ∀ v ∈ e, v ∈ (A : Set V) := Iff.rfl

theorem mem_touchOf {A : Finset V} {e : Sym2 V} :
    e ∈ touchOf A ↔ ∃ v ∈ (A : Set V), v ∈ e := Iff.rfl

/-- An unordered pair with two distinct endpoints is the pair they span. -/
theorem sym2_eq_of_mem_of_mem {e : Sym2 V} {v w : V} (hne : v ≠ w) (hv : v ∈ e) (hw : w ∈ e) :
    e = s(v, w) := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [Sym2.mem_iff] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · rw [Sym2.eq_swap]
    · exact absurd rfl hne

/-- **A path from `o ∈ A` to a vertex outside `A` must use an open edge that meets `A` and leaves
it.** -/
theorem exists_leaving_edge {A : Finset V} {ω : Config V} {o v : V}
    (ho : o ∈ (A : Set V)) (hv : v ∉ (A : Set V)) (h : Connects ω o v) :
    ∃ e ∈ touchOf A, e ∉ inside A ∧ e ∈ ω := by
  rw [Connects, SimpleGraph.reachable_iff_reflTransGen] at h
  have key : ∀ {x : V}, Relation.ReflTransGen (openGraph ω).Adj o x →
      x ∈ (A : Set V) ∨ ∃ e ∈ touchOf A, e ∉ inside A ∧ e ∈ ω := by
    intro x hx
    induction hx with
    | refl => exact Or.inl ho
    | @tail u v _ huv ih =>
      rcases ih with huA | hex
      · by_cases hvA : v ∈ (A : Set V)
        · exact Or.inl hvA
        · rw [openGraph_adj] at huv
          refine Or.inr ⟨s(u, v), ⟨u, huA, Sym2.mem_mk_left u v⟩, ?_, huv.2⟩
          intro hmem
          exact hvA (hmem v (Sym2.mem_mk_right u v))
      · exact Or.inr hex
  rcases key h with hA | hex
  · exact absurd hA hv
  · exact hex

/-- **If every edge leaving `A` is closed, the cluster of `o ∈ A` stays inside `A`.** -/
theorem cluster_subset_of_leaving_closed {A : Finset V} {ω : Config V} {o : V}
    (ho : o ∈ (A : Set V))
    (hclosed : ∀ e ∈ touchOf A, e ∉ inside A → e ∉ ω) :
    cluster ω o ⊆ (A : Set V) := by
  intro x hx
  by_contra hx'
  obtain ⟨e, heA, heout, heω⟩ := exists_leaving_edge ho hx' (mem_cluster_iff.mp hx)
  exact hclosed e heA heout heω

/-- **If the cluster of `o` is contained in `A` and `o ∈ A`, then every vertex of `A` is connected
to `o` using only edges inside `A`.** -/
theorem connects_inside_of_cluster_subset {A : Finset V} {ω : Config V} {o : V}
    (ho : o ∈ (A : Set V)) (hA : cluster ω o ⊆ (A : Set V)) {x : V} (hx : Connects ω o x) :
    Connects (ω ∩ inside A) o x := by
  have hx' : Relation.ReflTransGen (openGraph ω).Adj o x := by
    rw [Connects, SimpleGraph.reachable_iff_reflTransGen] at hx
    exact hx
  have key : ∀ {x : V}, Relation.ReflTransGen (openGraph ω).Adj o x →
      x ∈ (A : Set V) ∧ Relation.ReflTransGen (openGraph (ω ∩ inside A)).Adj o x := by
    intro x hxx
    induction hxx with
    | refl => exact ⟨ho, Relation.ReflTransGen.refl⟩
    | @tail u v _ huv ih =>
      obtain ⟨huA, ihu⟩ := ih
      have huv' : u ≠ v ∧ s(u, v) ∈ ω := by
        rw [openGraph_adj] at huv
        exact huv
      have huConnC : Connects ω o u :=
        connects_mono Set.inter_subset_left (by
          rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
          exact ihu)
      have huConn : Relation.ReflTransGen (openGraph ω).Adj o u := by
        rw [Connects, SimpleGraph.reachable_iff_reflTransGen] at huConnC
        exact huConnC
      have hvConn : Relation.ReflTransGen (openGraph ω).Adj o v := huConn.tail huv
      have hvA : v ∈ (A : Set V) := hA (mem_cluster_iff.mpr (by
        rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
        exact hvConn))
      have hedge : s(u, v) ∈ inside A := fun w hw => by
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact huA
        · exact hvA
      refine ⟨hvA, ihu.tail ?_⟩
      rw [openGraph_adj]
      exact ⟨huv'.1, huv'.2, hedge⟩
  rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
  exact (key hx').2

/-- **The cluster of `o` is the finite set `A` (with `o ∈ A`) iff `A` is connected to `o` inside
`A` and every edge leaving `A` is closed.** -/
theorem cluster_eq_finset_iff {A : Finset V} {ω : Config V} {o : V} (ho : o ∈ (A : Set V)) :
    cluster ω o = (A : Set V) ↔
      (∀ a ∈ A, Connects (ω ∩ inside A) o a) ∧
        (∀ e ∈ touchOf A, e ∉ inside A → e ∉ ω) := by
  constructor
  · intro hcl
    have hsub : cluster ω o ⊆ (A : Set V) := hcl.le
    refine ⟨fun a ha => connects_inside_of_cluster_subset ho hsub (mem_cluster_iff.mp ?_), ?_⟩
    · rw [hcl]; exact ha
    · intro e heA heout heω
      obtain ⟨v, hvA, hve⟩ := mem_touchOf.mp heA
      have hwn : ∃ w ∈ e, w ∉ (A : Set V) := by
        by_contra hcon
        exact heout (fun w hw => by
          by_contra hwA
          exact hcon ⟨w, hw, hwA⟩)
      obtain ⟨w, hwe, hwA⟩ := hwn
      have hvne : v ≠ w := fun h => hwA (h ▸ hvA)
      have hedgeq : e = s(v, w) := sym2_eq_of_mem_of_mem hvne hve hwe
      have hadj : (openGraph ω).Adj v w := by
        rw [openGraph_adj]
        refine ⟨hvne, ?_⟩
        rw [← hedgeq]; exact heω
      have hvCluster : v ∈ cluster ω o := by rw [hcl]; exact hvA
      have hwCluster : w ∈ cluster ω o := mem_cluster_iff.mpr ((mem_cluster_iff.mp hvCluster).trans hadj.reachable)
      rw [hcl] at hwCluster
      exact hwA hwCluster
  · rintro ⟨hconn, hclosed⟩
    have hle : (A : Set V) ⊆ cluster ω o := by
      intro x hx
      exact mem_cluster_iff.mpr (connects_mono Set.inter_subset_left (hconn x hx))
    have hge : cluster ω o ⊆ (A : Set V) := cluster_subset_of_leaving_closed ho hclosed
    exact Set.Subset.antisymm hge hle

/-- If `o ∉ A` there is no configuration whose cluster of `o` is `A`. -/
theorem cluster_ne_finset_of_notMem {A : Finset V} {ω : Config V} {o : V}
    (ho : o ∉ (A : Set V)) : cluster ω o ≠ (A : Set V) := by
  intro h
  exact ho (h ▸ cluster_mem_self ω o)

end PercLib.CriticalLRP
