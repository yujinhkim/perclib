/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New deterministic glue using mathlib's existing connected-component quotient and
finite fiber sums at revision 56a005855ea17e0b0958f73ec801ae140b0a1679.
No new component quotient and no copied upstream proof.
-/
module

public import PercLib.Percolation.Bond.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

@[expose] public section

open Set SimpleGraph

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A cluster is the support of the existing mathlib connected component. -/
theorem cluster_eq_component_supp (ω : Config V) (v : V) :
    cluster ω v = ((openGraph ω).connectedComponentMk v).supp := by
  ext w
  simp only [cluster, Set.mem_ofPred_eq, ConnectedComponent.mem_supp_iff,
    ConnectedComponent.eq, reachable_comm]

/-- Two roots have the same cluster precisely when they are connected. -/
theorem cluster_eq_iff_conn (ω : Config V) (u v : V) :
    cluster ω u = cluster ω v ↔ ω ∈ conn u v := by
  rw [cluster_eq_component_supp, cluster_eq_component_supp,
    ConnectedComponent.supp_inj, ConnectedComponent.eq]
  rfl

/-- Clusters form a partition, on arbitrary vertex types. -/
theorem cluster_eq_or_disjoint (ω : Config V) (u v : V) :
    cluster ω u = cluster ω v ∨ Disjoint (cluster ω u) (cluster ω v) := by
  by_cases h : cluster ω u = cluster ω v
  · exact Or.inl h
  · right
    rw [cluster_eq_component_supp, cluster_eq_component_supp]
    apply pairwise_disjoint_supp_connectedComponent
    intro hc
    exact h (by simp only [cluster_eq_component_supp, hc])

/-- A root in a component has that component as its cluster. -/
theorem cluster_eq_supp_of_mem (ω : Config V) (C : (openGraph ω).ConnectedComponent)
    {v : V} (hv : v ∈ C.supp) : cluster ω v = C.supp := by
  rw [cluster_eq_component_supp, (ConnectedComponent.mem_supp_iff C v).mp hv]

/-- Summing any natural-valued function of cluster size by connected components.
Both sums are finite because the vertex type is finite. -/
theorem tsum_cluster_ncard_function [Finite V] (ω : Config V) (f : ℕ → ℕ) :
    ∑' v : V, f (cluster ω v).ncard =
      ∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard * f C.supp.ncard := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype (openGraph ω).ConnectedComponent := Fintype.ofFinite _
  simp only [tsum_fintype]
  rw [← Fintype.sum_fiberwise (openGraph ω).connectedComponentMk]
  apply Finset.sum_congr rfl
  intro C _
  have hc : ∀ v : {v // (openGraph ω).connectedComponentMk v = C},
      cluster ω v = C.supp := fun v => cluster_eq_supp_of_mem ω C v.2
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  exact_mod_cast Set.fintypeCard_eq_ncard C.supp

/-- The sum of cluster sizes equals the sum of squared component sizes. -/
theorem tsum_cluster_ncard_eq_tsum_component_sq [Finite V] (ω : Config V) :
    ∑' v : V, (cluster ω v).ncard =
      ∑' C : (openGraph ω).ConnectedComponent, C.supp.ncard ^ 2 := by
  simpa only [sq, id_eq] using tsum_cluster_ncard_function ω id

/-- The same partition identity for a real function of cluster size. -/
theorem tsum_cluster_real_function [Finite V] (ω : Config V) (f : ℕ → ℝ) :
    ∑' v : V, f (cluster ω v).ncard =
      ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) * f C.supp.ncard := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Fintype (openGraph ω).ConnectedComponent := Fintype.ofFinite _
  simp only [tsum_fintype]
  rw [← Fintype.sum_fiberwise (openGraph ω).connectedComponentMk]
  apply Finset.sum_congr rfl
  intro C _
  have hc : ∀ v : {v // (openGraph ω).connectedComponentMk v = C},
      cluster ω v = C.supp := fun v => cluster_eq_supp_of_mem ω C v.2
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  exact congrArg Nat.cast (Set.fintypeCard_eq_ncard C.supp)

/-- For a finite domain, paths and components are taken inside the induced graph.
This is not the intersection of an ambient cluster with the domain. -/
theorem tsum_internal_cluster_ncard (ω : Config V) (Λ : Set V) [Finite Λ] :
    ∑' v : Λ, {w : Λ | ((openGraph ω).induce Λ).Reachable v w}.ncard =
      ∑' C : ((openGraph ω).induce Λ).ConnectedComponent, C.supp.ncard ^ 2 := by
  have h := tsum_cluster_ncard_eq_tsum_component_sq ((openGraph ω).induce Λ).edgeSet
  unfold cluster at h
  rw [show openGraph ((openGraph ω).induce Λ).edgeSet = (openGraph ω).induce Λ from
    SimpleGraph.fromEdgeSet_edgeSet _] at h
  exact h

-- Two isolated vertices each contribute one, rather than zero.
example : ∑' v : Bool, (cluster (∅ : Config Bool) v).ncard = 2 := by
  simp [tsum_fintype, cluster_empty]

-- With their edge open both vertices lie in a component of size two.
example : ∑' v : Bool, (cluster (Set.univ : Config Bool) v).ncard = 4 := by
  have hc (v : Bool) : cluster (Set.univ : Config Bool) v = Set.univ := by
    ext w
    simp [cluster, openGraph, SimpleGraph.fromEdgeSet_univ]
  simp [hc, tsum_fintype]

-- Empty vertex types are covered too.
example : ∑' v : Empty, (cluster (∅ : Config Empty) v).ncard = 0 := by simp

end PercLib.Percolation.Bond
