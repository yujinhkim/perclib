/-
Swarm `smwxk27m7`, member `m1`, direction `d2` (`J3-EVENT-BRIDGE`).

The genuine event-level regrouping at split position `j = 3`.

At `j = 3` the sixth arm `t — c` lands on comb arm `3`, i.e. on the arm `b₃ — w`; the
split tree is the mirror image of the `j = 0` tree across `u ↔ w`, and `Defs.lean`'s
`slotProd2 π 3` names the star set `{u, w}` read off the actual `CombSystem` data:

* star at `u` with leaves `b₀, b₁, v`  → joint group `conn b₀ v ∩ conn b₁ v`;
* star at `w` with leaves `b₄, c, v`  → joint group `conn b₄ v ∩ conn c v`;
* residual edges `b₂ — v`, `b₃ — c`, `t — c`.

Nothing is assumed: the decomposition is *read off* the nine pairwise edge-disjoint walks of
`combSystem_nine`, including the fact that `c` lies on arm `3` (`A.edges ++ B.edges = p3.edges`).
No independence, no product of probabilities, no finiteness, no `hpoint`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.J3.Defs

/-!
# The `j = 3` two-joint/three-single regrouping
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeExpansion.SixPoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval2.J3

variable {V : Type*}

/-- **`k = 2` regrouping at split position `3`.**  The star at `u` has leaves `b₀, b₁, v`;
the star at `w` has leaves `b₄, c, v`; the three two-point factors are `b₂ — v`, `b₃ — c`
and `t — c`.  This is the mirror of `SplitPattern.combSystem_twoJointThree_zero` across
`u ↔ w` with the split arm moved from `0` to `3`. -/
theorem combSystem_twoJointThree_three [Countable V] (b0 b1 b2 b3 b4 t u v w c : V) :
    {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 3} ⊆
      TwoJointThreeCert (V := V) (conn b0 v ∩ conn b1 v) (conn b4 v ∩ conn c v)
        (conn b2 v) (conn b3 c) (conn t c) := by
  rintro ω h
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, _hsplit, _hnodup, hfamD, _hAn, _hBn, _hQn,
    hAB, hAi, hBi, hQi, hAQ, hBQ, _hc⟩ := combSystem_nine h
  refine fiveGroup_of_two_stars (ω := ω)
    ⟨u, b0, b1, v, p0, p1, s1⟩ ⟨w, b4, c, v, p4, B, s2.reverse⟩
    ![⟨(b2, v), p2⟩, ⟨(b3, c), A⟩, ⟨(t, c), Q⟩] ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the two stars are disjoint
    refine disjoint_union3_union3
      (disjoint_walkEdges p0 p4 (hfamD 0 4 (by decide)))
      (disjoint_walkEdges p0 B (hBi 0 (by decide)).symm)
      ?_ (disjoint_walkEdges p1 p4 (hfamD 1 4 (by decide)))
      (disjoint_walkEdges p1 B (hBi 1 (by decide)).symm) ?_
      (disjoint_walkEdges s1 p4 (hfamD 5 4 (by decide)))
      (disjoint_walkEdges s1 B (hBi 5 (by decide)).symm) ?_
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges p0 s2 (hfamD 0 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges p1 s2 (hfamD 1 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges s1 s2 (hfamD 5 6 (by decide))
  · -- the first star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p0 p2 (hfamD 0 2 (by decide)))
        (disjoint_walkEdges p1 p2 (hfamD 1 2 (by decide)))
        (disjoint_walkEdges s1 p2 (hfamD 5 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p0 A (hAi 0 (by decide)).symm)
        (disjoint_walkEdges p1 A (hAi 1 (by decide)).symm)
        (disjoint_walkEdges s1 A (hAi 5 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p0 (hQi 0)).symm
        (disjoint_walkEdges Q p1 (hQi 1)).symm
        (disjoint_walkEdges Q s1 (hQi 5)).symm
  · -- the second star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p4 p2 (hfamD 4 2 (by decide)))
        (disjoint_walkEdges B p2 (hBi 2 (by decide)))
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 p2 (hfamD 6 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p4 A (hAi 4 (by decide)).symm)
        (disjoint_walkEdges B A hAB.symm)
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 A (hAi 6 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p4 (hQi 4)).symm
        (disjoint_walkEdges Q B hBQ.symm).symm
        (by rw [walkEdges_reverse]
            exact (disjoint_walkEdges Q s2 (hQi 6)).symm)
  · -- the three single walks are pairwise disjoint
    intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact disjoint_walkEdges p2 A (hAi 2 (by decide)).symm
    · exact disjoint_walkEdges p2 Q (hQi 2).symm
    · exact disjoint_walkEdges A p2 (hAi 2 (by decide))
    · exact absurd rfl hik
    · exact disjoint_walkEdges A Q hAQ
    · exact disjoint_walkEdges Q p2 (hQi 2)
    · exact disjoint_walkEdges Q A hAQ.symm
    · exact absurd rfl hik

/-! ## Source faithfulness: `{u, w}` is the star set of the split-`3` tree

The event inclusion above is stated for the `CombSystem` slot convention, not for the abstract
split tree.  The two checks below tie it to `SplitPattern`: at split position `3` the split arm
is arm `3` (`b₃ — w`), the neighbours of `u` (index `6`) are `b₀, b₁, v` and the neighbours of
`w` (index `8`) are `b₄, v, c`, with residual edges `b₂ — v`, `t — c`, `b₃ — c`.  This is
exactly the star set `{u, w}` that `slotProd2 π 3` names, and `(6, 8)` is one of the three
admissible independent pairs tabulated by `SplitPattern.indepTable`. -/

/-- **The `k = 2` pattern at split position `3`, star set `{u, w}`.** -/
theorem pattern_three :
    nbrs 3 6 = [0, 1, 7] ∧ nbrs 3 8 = [4, 7, 9] ∧
      residual 3 6 8 = [(2, 7), (5, 9), (3, 9)] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `{u, w}` is an admissible star set at split position `3`. -/
theorem starSet_three_mem : ((6, 8) : ℕ × ℕ) ∈ indepPairs 3 := by decide

/-- **The five groups of `TwoJointThreeCert` read off the split tree.**  The two joint groups are
the two stars (spine target `v`, index `7`), and the three two-point groups are the residual
edges.  This is the `j = 3` analogue of `SplitPattern.production_pattern_events`; the index
identifications `vert 6 = u`, `vert 7 = v`, `vert 8 = w`, `vert 9 = c` are `rfl`. -/
theorem pattern_three_events (b0 b1 b2 b3 b4 t u v w c : V) :
    (conn (vert b0 b1 b2 b3 b4 t u v w c 0) (vert b0 b1 b2 b3 b4 t u v w c 7) ∩
        conn (vert b0 b1 b2 b3 b4 t u v w c 1) (vert b0 b1 b2 b3 b4 t u v w c 7)) =
      (conn b0 v ∩ conn b1 v) ∧
    (conn (vert b0 b1 b2 b3 b4 t u v w c 4) (vert b0 b1 b2 b3 b4 t u v w c 7) ∩
        conn (vert b0 b1 b2 b3 b4 t u v w c 9) (vert b0 b1 b2 b3 b4 t u v w c 7)) =
      (conn b4 v ∩ conn c v) ∧
    conn (vert b0 b1 b2 b3 b4 t u v w c 2) (vert b0 b1 b2 b3 b4 t u v w c 7) = conn b2 v ∧
    conn (vert b0 b1 b2 b3 b4 t u v w c 3) (vert b0 b1 b2 b3 b4 t u v w c 9) = conn b3 c ∧
    conn (vert b0 b1 b2 b3 b4 t u v w c 5) (vert b0 b1 b2 b3 b4 t u v w c 9) = conn t c := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [vert]

end PercLib.CriticalLRP.SixPoint.SplitEval2.J3
