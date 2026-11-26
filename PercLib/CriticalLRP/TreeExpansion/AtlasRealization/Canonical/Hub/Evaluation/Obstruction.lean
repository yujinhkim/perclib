/- Independently rebuilt from `smwx3hvzx`, member `m1` finding f1.
Production integration revision: `c491c66109f24f38fa27cbccbcc52d11a14a8c33`.

A checked obstruction: the three-point function at the hub is *strictly* weaker than the joint
(disjoint-occurrence) hub diagram, and the two are not interchangeable.

Source: Lemma I.4.16 of T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, p. 44.  The source bounds the hub diagram by BK and then sums the
three-point function; this file records, as a proved statement, that the direction
`jointP-event ⊆ hub-diagram` is *false*, so the comparison made in
`HubJointEval/SourceDiag.lean` (`hubDiagJoint ⊆ hubPairJoint`, hence
`law hubDiagJoint ≤ jointP`) is the only valid one and the two objects must be kept apart.

## The obstruction

On `V = Fin 2` with the single open pair `{0,1}`:
* the three-point event `0 <-> 1 and 0 <-> 1` holds (both connections use the one open pair);
* the joint three-arm event with three arms `1 <-> 0` fails: every witness for `1 <-> 0` must
  contain the pair `{0,1}`, so the three pairwise disjoint witnesses demanded by `DisjFam` cannot
  exist.

This is also the *repeated physical vertex* case: the three arms have the same far endpoint, and
they remain three separate slots.  The duplicated data is not merged and not dropped; it is
precisely what makes the joint event smaller than the three-point function.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Evaluation.SourceDiag

/-!
# The disjointness obstruction
-/

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal BigOperators

open PercLib.CriticalLRP (Config Connects connSet openGraph openGraph_adj openGraph_empty)
open PercLib.CriticalLRP.Percolation (DisjFam)

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace HubJointEval

/-- The single open pair connects `1` to `0`. -/
theorem connects_oneEdgeConfig : Connects oneEdgeConfig (1 : Fin 2) 0 := by
  have hadj : (openGraph oneEdgeConfig).Adj (0 : Fin 2) 1 := by
    rw [openGraph_adj]
    exact ⟨by decide, Set.mem_singleton _⟩
  exact SimpleGraph.Reachable.symm (SimpleGraph.Adj.reachable hadj)

/-- **Every witness for `1 <-> 0` inside the single-pair configuration contains that pair.** -/
theorem pair_mem_of_witness (W : Finset (Sym2 (Fin 2)))
    (hW : (W : Set (Sym2 (Fin 2))) ⊆ oneEdgeConfig)
    (hconn : Connects (W : Set (Sym2 (Fin 2))) (1 : Fin 2) 0) :
    s(0, 1) ∈ W := by
  by_contra h
  have hempty : (W : Set (Sym2 (Fin 2))) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro e he
    have h1 : e = s(0, 1) := hW he
    exact h (h1 ▸ he)
  rw [hempty] at hconn
  have h2 : (openGraph (∅ : Set (Sym2 (Fin 2)))).Reachable (1 : Fin 2) 0 := hconn
  rw [openGraph_empty, SimpleGraph.reachable_bot] at h2
  exact absurd h2 (by decide)

/-- **The three-point function at the hub does not imply the joint three-arm event.**

With three arms all ending at the same vertex `1` and hub `0`, in the single-pair configuration
the three-point event holds but the joint (pairwise edge-disjoint) event does not.  Hence the
comparison `law (hubArmJoint) ≤ jointP` of `HubJointEval/Bridge.lean` cannot be reversed, and no
proof may replace the joint hub value by the three-point function in the *lower* direction. -/
theorem hubPairJoint_not_subset_hubArmJoint :
    ¬ (hubPairJoint (1 : Fin 2) 1 0 ⊆ hubArmJoint (0 : Fin 2) (fun _ => 1)) := by
  intro hsub
  have hpair : oneEdgeConfig ∈ hubPairJoint (1 : Fin 2) 1 0 :=
    ⟨connects_oneEdgeConfig, connects_oneEdgeConfig⟩
  obtain ⟨W, hsubW, hmem, hdisj⟩ := hsub hpair
  have h0 : s(0, 1) ∈ W 0 := pair_mem_of_witness (W 0) (hsubW 0) (hmem 0)
  have h1 : s(0, 1) ∈ W 1 := pair_mem_of_witness (W 1) (hsubW 1) (hmem 1)
  have hd : Disjoint (W 0) (W 1) := hdisj 0 1 (by decide)
  exact (Finset.disjoint_left.mp hd) h0 h1

end HubJointEval
