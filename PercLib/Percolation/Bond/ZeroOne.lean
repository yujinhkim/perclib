/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 118 (Q-2), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Cylinder
public import PercLib.Probability.OpenEventHarris
public import PercLib.Probability.ZeroOne

/-!
# The zero-one law for the existence of an infinite cluster

Opening one more pair joins at most three clusters, so it creates an infinite cluster
only if one already exists (`exists_cluster_infinite_insert_iff`). The event that some
cluster is infinite is therefore invariant under finite modification, and its probability
is `0` or `1` (`law_exists_cluster_infinite_eq_zero_or_one`). This file adds no
definition.

The zero-one law is not claimed for the event that the cluster of a fixed vertex is
infinite: that event is not invariant under finite modification.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **Opening one pair joins at most three clusters.** Every vertex joined to `x` after
`s(a, b)` is opened was already joined to `x`, to `a` or to `b`. -/
theorem cluster_insert_subset (ω : Config V) (a b x : V) :
    cluster (insert s(a, b) ω) x ⊆ cluster ω x ∪ cluster ω a ∪ cluster ω b := by
  intro y hy
  change (openGraph (insert s(a, b) ω)).Reachable x y at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact Or.inl (Or.inl (mem_cluster_self ω x))
  | @tail z w _ hadj ih =>
    rw [openGraph_adj_iff, mem_insert_iff] at hadj
    obtain ⟨he | he, hne⟩ := hadj
    · rcases Sym2.eq_iff.1 he with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr (mem_cluster_self ω _)
      · exact Or.inl (Or.inr (mem_cluster_self ω _))
    · have hzw : (openGraph ω).Reachable z w :=
        SimpleGraph.Adj.reachable ((openGraph_adj_iff ω z w).2 ⟨he, hne⟩)
      rcases ih with (h | h) | h
      · exact Or.inl (Or.inl (SimpleGraph.Reachable.trans h hzw))
      · exact Or.inl (Or.inr (SimpleGraph.Reachable.trans h hzw))
      · exact Or.inr (SimpleGraph.Reachable.trans h hzw)

/-- **Opening one pair does not change whether an infinite cluster exists.** -/
theorem exists_cluster_infinite_insert_iff (ω : Config V) (e : Sym2 V) :
    (∃ x, (cluster (insert e ω) x).Infinite) ↔ ∃ x, (cluster ω x).Infinite := by
  constructor
  · rintro ⟨x, hx⟩
    induction e using Sym2.ind with
    | _ a b =>
      have h := hx.mono (cluster_insert_subset ω a b x)
      rcases infinite_union.1 h with h | h
      · rcases infinite_union.1 h with h | h
        · exact ⟨x, h⟩
        · exact ⟨a, h⟩
      · exact ⟨b, h⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.mono (cluster_mono (subset_insert e ω) x)⟩

/-- The existence of an infinite cluster is measurable when there are countably many
vertices. -/
theorem measurableSet_exists_cluster_infinite [Countable V] :
    MeasurableSet {ω : Config V | ∃ x, (cluster ω x).Infinite} := by
  rw [ofPred_exists]
  exact MeasurableSet.iUnion fun x => measurableSet_cluster_infinite x

/-- **Zero-one law for percolation.** For every profile, an infinite cluster exists with
probability `0` or `1`. -/
theorem law_exists_cluster_infinite_eq_zero_or_one [Countable V]
    (q : Sym2 V → unitInterval) :
    law q {ω | ∃ x, (cluster ω x).Infinite} = 0 ∨
      law q {ω | ∃ x, (cluster ω x).Infinite} = 1 :=
  prodBernoulli_eq_zero_or_one_of_insert_iff q measurableSet_exists_cluster_infinite
    fun ω e => exists_cluster_infinite_insert_iff ω e

/-! Non-vacuity: both values occur. With every pair closed almost surely there is no
infinite cluster; on `ℕ` with every pair open almost surely the whole of `ℕ` is one
cluster. -/

/-- At `q = 0` almost surely no pair is open, so no cluster is infinite. -/
example [Countable V] :
    law (fun _ : Sym2 V => (0 : unitInterval)) {ω | ∃ x, (cluster ω x).Infinite} = 0 := by
  refine measure_mono_null (t := ⋃ e : Sym2 V, {ω : Config V | e ∈ ω}) ?_ ?_
  · rintro ω ⟨x, hx⟩
    by_contra h
    simp only [mem_iUnion, mem_ofPred_eq, not_exists] at h
    have : ω = ∅ := eq_empty_of_forall_notMem h
    subst this
    rw [cluster_empty] at hx
    exact hx (finite_singleton x)
  · exact measure_iUnion_null fun e => by
      simpa [law] using prodBernoulli_setOf_mem (fun _ : Sym2 V => (0 : unitInterval)) e

/-- On `ℕ` at `q = 1` almost surely every pair is open, so the cluster of `0` is `ℕ`. -/
example : law (fun _ : Sym2 ℕ => (1 : unitInterval)) {ω | ∃ x, (cluster ω x).Infinite} = 1 := by
  refine (prob_compl_eq_zero_iff measurableSet_exists_cluster_infinite).1 ?_
  refine measure_mono_null (t := ⋃ e : Sym2 ℕ, {ω : Config ℕ | e ∈ ω}ᶜ) ?_ ?_
  · intro ω hω
    by_contra h
    simp only [mem_iUnion, mem_compl_iff, mem_ofPred_eq, not_exists, not_not] at h
    refine hω ⟨0, ?_⟩
    have : cluster ω 0 = univ := eq_univ_of_forall fun y => by
      by_cases hy : (0 : ℕ) = y
      · rw [← hy]; exact mem_cluster_self ω 0
      · exact mem_conn_of_mem hy (h _)
    rw [this]
    exact infinite_univ
  · refine measure_iUnion_null fun e => (prob_compl_eq_zero_iff (measurableSet_mem e)).2 ?_
    simpa [law] using prodBernoulli_setOf_mem (fun _ : Sym2 ℕ => (1 : unitInterval)) e

end PercLib.Percolation.Bond
