/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The event inclusion `disjSet ⊆ pairDisjSet` fails: an explicit witness

`HgapClusterWeights.pairDisjSet_eq_disjSet_inter` identifies the model's disjoint weight with
`{o↔x ↮ y↔z} ∩ {y ∉ K_0}`.  This file records that the condition `y ∉ K_0` cannot be dropped:
in the canonical model on `Fin 4` with the four edges `0—1, 1—2, 2—3, 0—3` open, the two
connections `0↔1` and `2↔3` are disjointly witnessed (by the single edges `{0,1}` and `{2,3}`),
while `y = 2` **is** in the cluster of `0` (via `2—1—0`).  So this configuration lies in
`disjSet 0 1 2 3` and not in `pairDisjSet 0 1 2 3`.

Consequently the constant-`1` cluster-coordinate bound `edgeMeasure_gap_cluster_sharp` cannot be
obtained from the disjoint-occurrence bound by an event inclusion; its hypothesis `hrest` is a
genuine extra (restoration) input.  Nothing here is a statement about probabilities: the cylinder
of this configuration is a non-empty finite-edge cylinder, and each of its four edges has open
probability `π e > 0` in any non-degenerate model.
-/
module

public import PercLib.CriticalLRP.Correlation.HgapClusterWeights

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

/-- The four edges `0—1`, `1—2`, `2—3`, `0—3` on `Fin 4`. -/
def squareEdges : Finset (Sym2 (Fin 4)) := {s(0, 1), s(1, 2), s(2, 3), s(0, 3)}

/-- The configuration with exactly those four edges open. -/
def squareConfig : Config (Fin 4) := (squareEdges : Set (Sym2 (Fin 4)))

theorem mem_squareEdges {e : Sym2 (Fin 4)} (h : e ∈ squareEdges) : e ∈ squareConfig := h

theorem adj_01 : (openGraph squareConfig).Adj 0 1 := by
  rw [openGraph_adj]
  exact ⟨by decide, mem_squareEdges (by decide)⟩

theorem adj_12 : (openGraph squareConfig).Adj 1 2 := by
  rw [openGraph_adj]
  exact ⟨by decide, mem_squareEdges (by decide)⟩

theorem adj_23 : (openGraph squareConfig).Adj 2 3 := by
  rw [openGraph_adj]
  exact ⟨by decide, mem_squareEdges (by decide)⟩

theorem conn_01 : Connects squareConfig 0 1 := ⟨SimpleGraph.Walk.cons adj_01 SimpleGraph.Walk.nil⟩

theorem conn_12 : Connects squareConfig 1 2 := ⟨SimpleGraph.Walk.cons adj_12 SimpleGraph.Walk.nil⟩

theorem conn_23 : Connects squareConfig 2 3 := ⟨SimpleGraph.Walk.cons adj_23 SimpleGraph.Walk.nil⟩

theorem conn_02 : Connects squareConfig 0 2 :=
  ⟨SimpleGraph.Walk.cons adj_01 (SimpleGraph.Walk.cons adj_12 SimpleGraph.Walk.nil)⟩

/-- The configuration lies in the disjoint-occurrence event `0↔1 ↮ 2↔3`. -/
theorem square_mem_disjSet : squareConfig ∈ disjSet 0 1 2 3 := by
  refine ⟨{s(0, 1)}, {s(2, 3)}, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_coe, Finset.mem_singleton] at he
    subst he
    exact mem_squareEdges (by decide)
  · intro e he
    rw [Finset.mem_coe, Finset.mem_singleton] at he
    subst he
    exact mem_squareEdges (by decide)
  · rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_singleton] at he he'
    exact (by decide : (s(0, 1) : Sym2 (Fin 4)) ≠ s(2, 3)) (he.symm.trans he')
  · -- `{0,1}` as a configuration connects `0` to `1`
    refine ⟨SimpleGraph.Walk.cons ?_ SimpleGraph.Walk.nil⟩
    rw [openGraph_adj]
    exact ⟨by decide, by rw [Finset.mem_coe]; exact (by decide : s(0, 1) ∈ ({s(0, 1)} : Finset (Sym2 (Fin 4))))⟩
  · refine ⟨SimpleGraph.Walk.cons ?_ SimpleGraph.Walk.nil⟩
    rw [openGraph_adj]
    exact ⟨by decide, by rw [Finset.mem_coe]; exact (by decide : s(2, 3) ∈ ({s(2, 3)} : Finset (Sym2 (Fin 4))))⟩

/-- The same configuration is **not** in the model's weight event, since `y = 2` lies in the
cluster of `0`. -/
theorem square_not_mem_pairDisjSet : squareConfig ∉ pairDisjSet 0 1 2 3 := by
  intro h
  exact h.1.2 conn_02

/-- Hence the unconditioned event inclusion `disjSet 0 1 2 3 ⊆ pairDisjSet 0 1 2 3` is false. -/
theorem not_disjSet_subset_pairDisjSet :
    ¬ (disjSet (0 : Fin 4) 1 2 3 ⊆ pairDisjSet (0 : Fin 4) 1 2 3) :=
  fun h => square_not_mem_pairDisjSet (h square_mem_disjSet)

end PercLib.CriticalLRP
