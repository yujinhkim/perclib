/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The edges touching a cluster, and their local (one-edge) determinacy

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.12 (p. 39): the rewiring set is

  `{e : e touches the cluster K_0 of 0 in ω}`,

and the construction relies on the following standard locality property, which is also the key
combinatorial input to the "restoration" (resampling) step: **whether an edge `e` touches the
cluster of `o` does not depend on the state of `e` itself**.  If a path from `o` to an endpoint of
`e` uses `e`, then the prefix of the path up to the other endpoint of `e` avoids `e` and already
connects `o` to an endpoint of `e`.

Consequences proved here:

* `connects_sdiff_singleton_or_endpoint` : a path from `o` either survives the deletion of `e` or
  already connects `o` to an endpoint of `e`;
* `mem_touchSet_sdiff_singleton` : `e` touches the cluster of `o` in `ω \ {e}` iff it does in `ω`;
* `mem_touchSet_forceOn_singleton` : replacing the state of `e` by anything leaves the statement
  "`e` touches the cluster of `o`" unchanged.

These are the one-edge instances of the locality used in the restoration argument.  The *global*
statement ("the configuration obtained by replacing the coordinates outside `S(ω)` by an
independent copy has the law of `ω`") is not proved here; see `README.md` in this directory for the
exact remaining step.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.BK.TwoCopy

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The set of **edges touching the cluster of `o`**. -/
def touchSet (ω : Config V) (o : V) : Set (Sym2 V) :=
  {e | ∃ v ∈ e, v ∈ cluster ω o}

theorem mem_touchSet {ω : Config V} {o : V} {e : Sym2 V} :
    e ∈ touchSet ω o ↔ ∃ v ∈ e, v ∈ cluster ω o := Iff.rfl

/-- Deleting a single edge gives a subconfiguration. -/
theorem sdiff_singleton_subset (ω : Config V) (e : Sym2 V) : ω \ {e} ⊆ ω := by
  intro e' he'
  have h := he'
  simp only [Set.mem_sdiff, Set.mem_singleton_iff] at h
  exact h.1

/-- The edge `s(a,b)` is different from `e` as soon as one of its endpoints is not in `e`;
used to keep track of the deleted edge along a path. -/
theorem sdiff_singleton_mem {ω : Config V} {e : Sym2 V} {a b : V}
    (h : s(a, b) ∈ ω) (hne : s(a, b) ≠ e) : s(a, b) ∈ ω \ {e} := by
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  exact ⟨h, hne⟩

/-- **A path from `o` either survives the deletion of `e`, or already connects `o` to an endpoint
of `e`.** -/
theorem reflTransGen_sdiff_singleton_or_endpoint {o v : V} {ω : Config V} {e : Sym2 V}
    (h : Relation.ReflTransGen (openGraph ω).Adj o v) :
    Relation.ReflTransGen (openGraph (ω \ {e})).Adj o v ∨
      ∃ w ∈ e, Relation.ReflTransGen (openGraph (ω \ {e})).Adj o w := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail a b hab hstep ih =>
    rcases ih with ih | ih
    · rw [openGraph_adj] at hstep
      by_cases he : s(a, b) = e
      · exact Or.inr ⟨a, he ▸ Sym2.mem_mk_left a b, ih⟩
      · exact Or.inl (ih.tail (by
          rw [openGraph_adj]
          exact ⟨hstep.1, sdiff_singleton_mem (ω := ω) hstep.2 he⟩))
    · exact Or.inr ih

/-- **`e` touches the cluster of `o` in `ω \ {e}` iff it does in `ω`.** -/
theorem mem_touchSet_sdiff_singleton {ω : Config V} {o : V} {e : Sym2 V} :
    e ∈ touchSet (ω \ {e}) o ↔ e ∈ touchSet ω o := by
  constructor
  · rintro ⟨v, hv, hcv⟩
    exact ⟨v, hv, cluster_mono (sdiff_singleton_subset ω e) o hcv⟩
  · rintro ⟨v, hv, hcv⟩
    have hconn : Connects ω o v := mem_cluster_iff.mp hcv
    rw [Connects, SimpleGraph.reachable_iff_reflTransGen] at hconn
    rcases reflTransGen_sdiff_singleton_or_endpoint hconn with h | h
    · exact ⟨v, hv, mem_cluster_iff.mpr (by
        rw [Connects, SimpleGraph.reachable_iff_reflTransGen]; exact h)⟩
    · obtain ⟨w, hw, hwc⟩ := h
      exact ⟨w, hw, mem_cluster_iff.mpr (by
        rw [Connects, SimpleGraph.reachable_iff_reflTransGen]; exact hwc)⟩

/-- The cluster of `o` in `ω \ {e}` is contained in the cluster of `o` in `ω`. -/
theorem cluster_sdiff_singleton_subset (ω : Config V) (o : V) (e : Sym2 V) :
    cluster (ω \ {e}) o ⊆ cluster ω o :=
  cluster_mono (sdiff_singleton_subset ω e) o

theorem forceOn_singleton_sdiff (η ω : Config V) (e : Sym2 V) :
    forceOn {e} η ω \ {e} = ω \ {e} := by
  ext e'
  by_cases he : e' = e
  · subst he
    simp [forceOn]
  · simp [forceOn, he]

/-- Replacing the state of a single edge `e` does not change whether `e` touches the cluster
of `o`. -/
theorem mem_touchSet_forceOn_singleton (ω η : Config V) (o : V) (e : Sym2 V) :
    e ∈ touchSet (forceOn {e} η ω) o ↔ e ∈ touchSet ω o := by
  calc e ∈ touchSet (forceOn {e} η ω) o
      ↔ e ∈ touchSet (forceOn {e} η ω \ {e}) o := (mem_touchSet_sdiff_singleton).symm
    _ ↔ e ∈ touchSet (ω \ {e}) o := by rw [forceOn_singleton_sdiff]
    _ ↔ e ∈ touchSet ω o := mem_touchSet_sdiff_singleton

end PercLib.CriticalLRP
