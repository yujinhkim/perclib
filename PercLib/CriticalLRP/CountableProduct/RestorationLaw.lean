/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Which coordinates decide the cluster, and the honest off-cluster factor

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Proposition I.3.1 (p. 29):

  "Since exploring the cluster of the origin in the cut-off model reveals only negative
   information about connectivity to the ghost off of this cluster, we have by these
   considerations and a union bound that (I.3.1)."

The companion file `GhostI35.lean` shows that the *cut-off* ghost-hit probability is not the
correct off-cluster factor: with the cut-off cluster `A` of the origin fixed, the edges with both
endpoints outside `A` are still i.i.d. with the **full** law, so the off-cluster ghost-hit
probability is a full-law quantity and can strictly exceed `ghostHits π_r h o`.

This file supplies the two structural facts behind that diagnosis.

* `cluster_eq_finset_congr`: for finite `A ∋ o`, `{cluster · o = A}` is decided by the edges
  *touching* `A` (`touchOf A`): two configurations that agree on those edges either both have
  cluster `A` or neither does.  So the exploration of the cut-off cluster indeed conditions only
  on a `touchOf A`-cylinder, and the complementary block keeps its product law.
* `cluster_condition_not_inner`: the hypothesis cannot be weakened to the edges with both
  endpoints *outside* `A`.  Two configurations that agree on every edge inside the complement of
  `A` may have different clusters at `o`.  Hence "the configuration off the cluster" alone does
  not determine the cluster event, and any factorisation must be stated in terms of the
  `touchOf A`-cylinder together with the untouched outer block.

Both are deterministic statements about `Config V = Set (Sym2 V)`; no probability is involved, so
they are the honest combinatorial core of the restoration step, free of any independence
assertion.  `example_offCluster_exceeds` in `GhostI35.lean` records the numerical consequence in
the counterexample: the off-cluster full-law factor `1 - e^{-3h} = 37/64` strictly exceeds the
cut-off ghost-hit probability `1 - e^{-h} = 1/4`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.ClusterFinset
public import PercLib.CriticalLRP.CountableProduct.GhostCutoffCounterexample

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- Every edge with both endpoints in `A` touches `A`. -/
theorem inside_subset_touchOf (A : Finset V) : inside A ⊆ touchOf A := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    rw [mem_touchOf]
    exact ⟨a, mem_inside.mp he a (Sym2.mem_mk_left a b), Sym2.mem_mk_left a b⟩

/-- **The event `{cluster · o = A}` is a `touchOf A`-cylinder.**

If two configurations agree on every edge with at least one endpoint in the finite set `A`, and
`o ∈ A`, then the cluster of `o` is `A` in one configuration if and only if it is `A` in the
other.  This is the deterministic content of "exploring the cluster of the origin reveals only
information about the edges touching it": after conditioning on `{cluster · o = A}`, the edges
with both endpoints outside `A` are untouched. -/
theorem cluster_eq_finset_congr {A : Finset V} {ω ω' : Config V} {o : V}
    (ho : o ∈ (A : Set V)) (h : ∀ e, e ∈ touchOf A → (e ∈ ω ↔ e ∈ ω')) :
    (cluster ω o = (A : Set V)) ↔ (cluster ω' o = (A : Set V)) := by
  rw [cluster_eq_finset_iff ho, cluster_eq_finset_iff ho]
  have hinside : ω ∩ inside A = ω' ∩ inside A := by
    ext e
    by_cases he : e ∈ inside A
    · have ht : e ∈ touchOf A := inside_subset_touchOf A he
      constructor
      · rintro ⟨hmem, -⟩; exact ⟨(h e ht).mp hmem, he⟩
      · rintro ⟨hmem, -⟩; exact ⟨(h e ht).mpr hmem, he⟩
    · simp [Set.mem_inter_iff, he]
  have hout : ∀ e ∈ touchOf A, e ∉ inside A → (e ∉ ω ↔ e ∉ ω') := by
    intro e he _
    exact not_iff_not.mpr (h e he)
  rw [hinside]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun e he hei => (hout e he hei).mp (h2 e he hei)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun e he hei => (hout e he hei).mpr (h2 e he hei)⟩

/-! ## Sharpness: the complement of `touchOf A` is not enough -/

/-- The single-edge configuration on `Fin 4` with the edge `{0,1}` open. -/
def singleEdgeConfig : Config (Fin 4) := {e | e = s(0, 1)}

/-- **In the single-edge configuration the cluster of `0` is `{0,1}`.** -/
theorem cluster_singleEdgeConfig : cluster singleEdgeConfig (0 : Fin 4) = {0, 1} := by
  ext x
  rw [mem_cluster_iff]
  constructor
  · intro hx
    rw [Connects, SimpleGraph.reachable_iff_reflTransGen] at hx
    have key : ∀ {y : Fin 4},
        Relation.ReflTransGen (openGraph singleEdgeConfig).Adj 0 y → y ∈ ({0, 1} : Set (Fin 4)) := by
      intro y hy
      induction hy with
      | refl => exact Set.mem_insert_iff.mpr (Or.inl rfl)
      | @tail u v _ huv ih =>
        rw [openGraph_adj] at huv
        have hu : u = 0 ∨ u = 1 := Set.mem_insert_iff.mp ih
        rcases hu with rfl | rfl
        · have h2 : s(0, v) = s(0, 1) := by simpa [singleEdgeConfig] using huv.2
          rw [Sym2.eq_iff] at h2
          rcases h2 with ⟨-, hv⟩ | ⟨h0, -⟩
          · subst hv; exact Set.mem_insert_iff.mpr (Or.inr rfl)
          · exact absurd h0 (by decide)
        · have h2 : s(1, v) = s(0, 1) := by simpa [singleEdgeConfig] using huv.2
          rw [Sym2.eq_iff] at h2
          rcases h2 with ⟨h1, -⟩ | ⟨-, hv⟩
          · exact absurd h1 (by decide)
          · subst hv; exact Set.mem_insert_iff.mpr (Or.inl rfl)
    exact key hx
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact connects_refl _ _
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact connects_of_open (by decide) (by simp [singleEdgeConfig])

/-- **The `touchOf` hypothesis of `cluster_eq_finset_congr` cannot be weakened to the edges
inside the complement.**

The empty configuration and the single-edge configuration `{0,1}` agree on every edge whose
endpoints both avoid `{0}`, but their clusters at `0` differ (`{0}` versus `{0,1}`).  Hence the
cluster event is *not* a function of the configuration off the cluster alone: the outer block
"sees" the cluster only through the `touchOf`-cylinder, exactly as `cluster_eq_finset_congr`
asserts. -/
theorem cluster_condition_not_inner :
    ∃ ω ω' : Config (Fin 4),
      (∀ e : Sym2 (Fin 4), (∀ v ∈ e, v ∉ ({0} : Set (Fin 4))) → (e ∈ ω ↔ e ∈ ω')) ∧
        cluster ω 0 ≠ cluster ω' 0 := by
  refine ⟨∅, singleEdgeConfig, ?_, ?_⟩
  · intro e he
    constructor
    · intro h; exact absurd h (by simp)
    · intro h
      have h1 : e = s(0, 1) := by simpa [singleEdgeConfig] using h
      subst h1
      exact he 0 (Sym2.mem_mk_left 0 1) rfl
  · rw [cluster_empty, cluster_singleEdgeConfig]
    intro h
    have h2 : (1 : Fin 4) ∈ ({0, 1} : Set (Fin 4)) := Set.mem_insert_iff.mpr (Or.inr rfl)
    rw [← h] at h2
    simp at h2

/-- The same sharpness statement at the level used in the paper: agreeing on all edges with
*both* endpoints outside `{0}` does not fix the cluster of `0`, so `{K_0 = A}` is not an outer
cylinder. -/
theorem cluster_condition_not_outer :
    ¬ ∀ ω ω' : Config (Fin 4),
      (∀ e : Sym2 (Fin 4), (∀ v ∈ e, v ∉ ({0} : Set (Fin 4))) → (e ∈ ω ↔ e ∈ ω')) →
        cluster ω 0 = cluster ω' 0 := by
  intro h
  obtain ⟨ω, ω', h1, h2⟩ := cluster_condition_not_inner
  exact h2 (h ω ω' h1)

end PercLib.CriticalLRP
