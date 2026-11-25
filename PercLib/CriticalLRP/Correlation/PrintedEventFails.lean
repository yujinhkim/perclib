/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The printed final step of Lemma I.4.12 is not an identity of events

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.12 (p. 39), last display:

  `P(0↔x)P(y↔z) − P(0↔x ↮ y↔z) = P(x ∈ K_0, z ∈ K̃_y) − P(x ∈ K_0, y ∉ K_0, z ∈ K_y)
     = P(x ∈ K_0, z ∈ K̃_y \ K_y)`.

Besides the failure of `K_y ⊆ K̃_y` in the printed coupling
(`not_cluster_subset_forceOn_compl`), the middle equality also needs the *identity of events*

  `{0↔x ↮ y↔z} = {x ∈ K_0, y ∉ K_0, z ∈ K_y}`

in the percolation configuration: the left-hand side is the disjoint-occurrence event of BK, the
right-hand side is a single-cluster event.  That equality is false: the left event is monotone in
the configuration, and it happens whenever there are two edge-disjoint connections `0↔x`, `y↔z`,
**whether or not** `y` is connected to `0`.  The four-vertex configuration below exhibits this:
`0↔1` on the edge `{0,1}` and `2↔3` on the edge `{2,3}` occur disjointly, while the vertex `2`
*is* in `K_0` (via the edge `{0,2}`), so the right-hand event fails.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.BK.CanonicalBridge

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The four-vertex configuration `{0,1}, {0,2}, {2,3}`. -/
def printedConfig : Config (Fin 4) := {s(0, 1), s(0, 2), s(2, 3)}

/-- A single open edge is a connection. -/
theorem connects_of_single {ω : Config V} {u v : V} (hne : u ≠ v) (hopen : s(u, v) ∈ ω) :
    Connects ω u v := by
  rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
  exact Relation.ReflTransGen.single (by rw [openGraph_adj]; exact ⟨hne, hopen⟩)

/-- `0` and `1` are joined in the configuration consisting of the single edge `{0,1}`. -/
theorem connects_singleton_zero_one (u v : V) (hne : u ≠ v) :
    Connects (({s(u, v)} : Finset (Sym2 V)) : Config V) u v := by
  rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
  refine Relation.ReflTransGen.single (by
    rw [openGraph_adj]
    exact ⟨hne, by simp⟩)

/-- In the printed configuration, `1 ↔ 0` and `2 ↔ 3` occur **disjointly**. -/
theorem printed_disjOcc :
    Percolation.DisjointOccurrence (connSet (0 : Fin 4) 1) (connSet 2 3) printedConfig := by
  refine ⟨{s(0, 1)}, {s(2, 3)}, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have hx : (s(0, 1) : Sym2 (Fin 4)) ∈ printedConfig := by
      simp only [printedConfig, Set.mem_insert_iff, Set.mem_singleton_iff]
      trivial
    have he' : e = s(0, 1) := by simpa using he
    rw [he']
    exact hx
  · intro e he
    have hx : (s(2, 3) : Sym2 (Fin 4)) ∈ printedConfig := by
      simp only [printedConfig, Set.mem_insert_iff, Set.mem_singleton_iff]
      trivial
    have he' : e = s(2, 3) := by simpa using he
    rw [he']
    exact hx
  · simp
  · exact connects_singleton_zero_one 0 1 (by decide)
  · exact connects_singleton_zero_one 2 3 (by decide)

/-- In the printed configuration the vertex `2` lies in the cluster of `0`. -/
theorem mem_cluster_printed_two : (2 : Fin 4) ∈ cluster printedConfig 0 :=
  mem_cluster_iff.mpr (connects_of_single (by decide) (by
    simp only [printedConfig, Set.mem_insert_iff, Set.mem_singleton_iff]
    trivial))

/-- **The printed identification `{0↔x ↮ y↔z} = {x ∈ K_0, y ∉ K_0, z ∈ K_y}` fails.** -/
theorem printed_event_identity_fails :
    ¬ ∀ (ω : Config (Fin 4)) (x y z : Fin 4),
        Percolation.DisjointOccurrence (connSet 0 x) (connSet y z) ω →
          (x ∈ cluster ω 0 ∧ y ∉ cluster ω 0 ∧ z ∈ cluster ω y) := by
  intro h
  have h2 := h printedConfig 1 2 3 printed_disjOcc
  exact h2.2.1 mem_cluster_printed_two

end PercLib.CriticalLRP
