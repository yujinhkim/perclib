/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Locality of the cluster under a single edge flip

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, proof of Lemma I.4.1 (the pivotal/flux sum) and
Lemma I.4.12 (the touching set).

The content of this file is purely combinatorial.  For a configuration `ω` and an
edge `e`:

* if a path from `o` in `ω ∪ {e}` ends at `v`, then either `o` is already
  connected to `v` in `ω`, or `o` is connected in `ω` to an endpoint of `e`
  (`reflTransGen_union_singleton_or_endpoint`);
* consequently, if `e` does not touch the cluster of `o` in `ω`, then opening `e`
  does not change that cluster (`cluster_union_singleton_eq`);
* and, since the touching set is invariant under the state of `e` itself
  (`mem_touchSet_forceOn_singleton`), replacing the state of `e` by anything
  leaves the cluster of `o` unchanged
  (`cluster_forceOn_singleton_eq_of_notMem_touchSet`).

These are the geometric inputs to the pivotal-flux estimates
(`RussoInf.Flux`): flipping an edge outside the touching set is invisible to any
functional of the cluster of `o`, and flipping an edge inside it is invisible as
soon as the value of the functional has saturated.
-/
module

public import PercLib.CriticalLRP.CountableProduct.EdgeTouch

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- Adding a single edge: a path from `o` to `v` in `ω ∪ {e}` either already exists in `ω`, or
reaches an endpoint of `e` in `ω`. -/
theorem reflTransGen_union_singleton_or_endpoint {o v : V} {ω : Config V} {e : Sym2 V}
    (h : Relation.ReflTransGen (openGraph (ω ∪ {e})).Adj o v) :
    Relation.ReflTransGen (openGraph ω).Adj o v ∨
      ∃ w ∈ e, Relation.ReflTransGen (openGraph ω).Adj o w := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail a b hab hstep ih =>
    have hne : a ≠ b := (openGraph_adj.mp hstep).1
    have hmem : s(a, b) ∈ ω ∪ {e} := (openGraph_adj.mp hstep).2
    by_cases he : s(a, b) = e
    · -- the last step is exactly the added edge
      rcases ih with ih | ⟨w, hw, hwc⟩
      · exact Or.inr ⟨a, he ▸ Sym2.mem_mk_left a b, ih⟩
      · exact Or.inr ⟨w, hw, hwc⟩
    · have hmemω : s(a, b) ∈ ω := by
        rw [Set.mem_union, Set.mem_singleton_iff] at hmem
        exact hmem.resolve_right he
      rcases ih with ih | ih
      · exact Or.inl (ih.tail (by rw [openGraph_adj]; exact ⟨hne, hmemω⟩))
      · exact Or.inr ih

/-- **Locality of the cluster under opening one edge.**  If `e` does not touch the cluster of `o`
in `ω`, then opening `e` does not change the cluster of `o`. -/
theorem cluster_union_singleton_eq {o : V} {ω : Config V} {e : Sym2 V}
    (h : e ∉ touchSet ω o) : cluster (ω ∪ {e}) o = cluster ω o := by
  refine Set.Subset.antisymm ?_ (cluster_mono Set.subset_union_left o)
  intro v hv
  have hconn : Connects (ω ∪ {e}) o v := mem_cluster_iff.mp hv
  rw [Connects, SimpleGraph.reachable_iff_reflTransGen] at hconn
  rcases reflTransGen_union_singleton_or_endpoint hconn with h' | ⟨w, hw, hwc⟩
  · exact mem_cluster_iff.mpr (by
      rw [Connects, SimpleGraph.reachable_iff_reflTransGen]; exact h')
  · exact absurd ⟨w, hw, mem_cluster_iff.mpr (by
      rw [Connects, SimpleGraph.reachable_iff_reflTransGen]; exact hwc)⟩ h

/-- The same statement for the configuration with `e` deleted: if `e` does not touch the cluster
of `o` in `ω`, then deleting `e` does not change that cluster. -/
theorem cluster_sdiff_singleton_eq {o : V} {ω : Config V} {e : Sym2 V}
    (h : e ∉ touchSet ω o) : cluster (ω \ {e}) o = cluster ω o := by
  have h' : e ∉ touchSet (ω \ {e}) o := by
    rw [mem_touchSet_sdiff_singleton]; exact h
  have hopen : cluster ((ω \ {e}) ∪ {e}) o = cluster (ω \ {e}) o :=
    cluster_union_singleton_eq h'
  have hsub : ω ⊆ (ω \ {e}) ∪ {e} := by
    intro e' he'
    by_cases hne : e' = e
    · subst hne; exact Set.mem_union_right _ (Set.mem_singleton_iff.mpr rfl)
    · exact Set.mem_union_left _ ⟨he', hne⟩
  refine Set.Subset.antisymm (cluster_mono (sdiff_singleton_subset ω e) o) ?_
  intro v hv
  rw [← hopen]
  exact cluster_mono hsub o hv

/-- **Locality under a single edge replacement.**  If `e` does not touch the cluster of `o` in
`ω`, then replacing the state of the edge `e` by anything at all leaves the cluster of `o`
unchanged. -/
theorem cluster_forceOn_singleton_eq_of_notMem_touchSet {o : V} {ω : Config V} {e : Sym2 V}
    (h : e ∉ touchSet ω o) (η : Config V) :
    cluster (forceOn {e} η ω) o = cluster ω o := by
  by_cases he : e ∈ η
  · have hfo : forceOn {e} η ω = ω ∪ {e} := by
      ext e'
      by_cases hne : e' = e
      · subst hne; simp [forceOn, he]
      · simp [forceOn, hne]
    rw [hfo]
    exact cluster_union_singleton_eq h
  · have hfo : forceOn {e} η ω = ω \ {e} := by
      ext e'
      by_cases hne : e' = e
      · subst hne; simp [forceOn, he]
      · simp [forceOn, hne]
    rw [hfo]
    exact cluster_sdiff_singleton_eq h

/-- Hence the cluster volume is unchanged as well. -/
theorem clusterVol_forceOn_singleton_eq_of_notMem_touchSet {o : V} {ω : Config V} {e : Sym2 V}
    (h : e ∉ touchSet ω o) (η : Config V) :
    clusterVol (forceOn {e} η ω) o = clusterVol ω o :=
  congrArg (fun S : Set V => (S.encard : ℝ≥0∞))
    (cluster_forceOn_singleton_eq_of_notMem_touchSet h η)

/-- And every function of the cluster of `o` is unchanged. -/
theorem apply_cluster_forceOn_singleton_eq_of_notMem_touchSet {o : V} {ω : Config V}
    {e : Sym2 V} (h : e ∉ touchSet ω o) (η : Config V) {α : Type*} (F : Set V → α) :
    F (cluster (forceOn {e} η ω) o) = F (cluster ω o) := by
  rw [cluster_forceOn_singleton_eq_of_notMem_touchSet h η]

end PercLib.CriticalLRP
