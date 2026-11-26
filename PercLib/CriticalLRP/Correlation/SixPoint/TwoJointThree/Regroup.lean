/-
Swarm `smwxdrsgz`, member `m3`, direction `SOURCE-FAITHFUL-HUB-COVER-REPAIR`.

The `p = 5`, `k = 2` regrouping of the nine edge-disjoint walks of the production
six-terminal arm system `SixPoint.CombSystem`, at the middle split `j = 2`.

Consumes: `SixPoint.CombSystem` (production, `Attachment/Defs.lean`) and
`SixPoint.combSystem_nine` (production, `Attachment/Split.lean`).
Produces: a `TwoJointThreeCert`, i.e. five pairwise edge-disjoint finite open
certificates carrying two *shared-spine* joint pairs and three two-point factors.

Every arm and every source vertex is preserved: the certificate sets are exactly
the edge sets of the nine walks, with the two spine pieces `s1`, `s2` each used
*inside* one joint group only.  No intersection is replaced by a disjoint
occurrence: the joint groups are `conn b0 v inter conn b1 v` and
`conn b3 v inter conn b4 v`, certified by a single set each.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointThree.Defs

/-!
# The regrouping of one middle `CombSystem` split

This is one event-certificate grouping, not a proved moment evaluation.
-/




open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- Edge lists of a walk and its reverse are disjoint from the same things. -/
theorem twoJoint_listDisjoint_rev {α : Type*} {a b : List α} (h : a.Disjoint b) :
    a.Disjoint b.reverse := by
  rw [List.disjoint_left] at *
  intro x hx hy
  exact h hx (List.mem_reverse.mp hy)

/-- **The `k = 2` regrouping at the middle split.**  A six-terminal arm system whose comb arm
`b2 - v` is split at the landing point `c` carries a two-joint/three-single certificate with
joint pairs `conn b0 v inter conn b1 v` and `conn b3 v inter conn b4 v` and two-point groups
`conn b2 c`, `conn c v`, `conn t c`.

Nine walks: `p0, p1, s1` (joint group 1), `p3, p4, s2.reverse` (joint group 2), and the
singletons `A : b2 - c`, `B : c - v`, `Q : t - c`. -/
theorem combSystem_twoJointThree [Countable V] (b0 b1 b2 b3 b4 t u v w c : V) :
    {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 2} ⊆
      TwoJointThreeCert (V := V) (conn b0 v ∩ conn b1 v) (conn b3 v ∩ conn b4 v)
        (conn b2 c) (conn c v) (conn t c) := by
  rintro ω h
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, _hABsplit, _hnodup, hfamD, _hAn, _hBn,
    _hQn, hAB, hAi, hBi, hQi, hAQ, hBQ, _hc⟩ := combSystem_nine h
  have e2 : (s2.reverse).edges = s2.edges.reverse := SimpleGraph.Walk.edges_reverse s2
  -- arm `i` against `B` / `A` / `Q`, correctly oriented
  have hAB' : ∀ i : Fin 7, i ≠ 2 → (combFam p0 p1 p2 p3 p4 s1 s2 i).edges.Disjoint A.edges :=
    fun i hi => (hAi i hi).symm
  have hBB' : ∀ i : Fin 7, i ≠ 2 → (combFam p0 p1 p2 p3 p4 s1 s2 i).edges.Disjoint B.edges :=
    fun i hi => (hBi i hi).symm
  have hQB' : ∀ i : Fin 7, (combFam p0 p1 p2 p3 p4 s1 s2 i).edges.Disjoint Q.edges :=
    fun i => (hQi i).symm
  -- arm `i` against the *reversed* spine `s2`
  have hs2r : ∀ i : Fin 7, i ≠ 6 →
      (combFam p0 p1 p2 p3 p4 s1 s2 i).edges.Disjoint (s2.reverse).edges := by
    intro i hi
    rw [e2]
    exact twoJoint_listDisjoint_rev (hfamD i 6 hi)
  -- reversed spine against `A`, `B`, `Q`
  have hs2A : (s2.reverse).edges.Disjoint A.edges := by
    rw [e2]; exact (twoJoint_listDisjoint_rev (hAi 6 (by decide))).symm
  have hs2B : (s2.reverse).edges.Disjoint B.edges := by
    rw [e2]; exact (twoJoint_listDisjoint_rev (hBi 6 (by decide))).symm
  have hQ6 : Q.edges.Disjoint (combFam p0 p1 p2 p3 p4 s1 s2 6).edges := hQi 6
  have hQ6' : (combFam p0 p1 p2 p3 p4 s1 s2 6).edges.Disjoint Q.edges := hQ6.symm
  have hs2Q : (s2.reverse).edges.Disjoint Q.edges := by
    rw [e2]; exact (twoJoint_listDisjoint_rev hQ6).symm
  -- group 1 pieces against the three singletons
  have h0A : Disjoint (walkEdges (p0.append s1)) (walkEdges A) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p0 A (hAB' 0 (by decide)),
       disjoint_walkEdges s1 A (hAB' 5 (by decide))⟩
  have h1A : Disjoint (walkEdges (p1.append s1)) (walkEdges A) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p1 A (hAB' 1 (by decide)),
       disjoint_walkEdges s1 A (hAB' 5 (by decide))⟩
  have h0B : Disjoint (walkEdges (p0.append s1)) (walkEdges B) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p0 B (hBB' 0 (by decide)),
       disjoint_walkEdges s1 B (hBB' 5 (by decide))⟩
  have h1B : Disjoint (walkEdges (p1.append s1)) (walkEdges B) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p1 B (hBB' 1 (by decide)),
       disjoint_walkEdges s1 B (hBB' 5 (by decide))⟩
  have h0Q : Disjoint (walkEdges (p0.append s1)) (walkEdges Q) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p0 Q (hQB' 0),
       disjoint_walkEdges s1 Q (hQB' 5)⟩
  have h1Q : Disjoint (walkEdges (p1.append s1)) (walkEdges Q) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p1 Q (hQB' 1),
       disjoint_walkEdges s1 Q (hQB' 5)⟩
  -- group 2 pieces against the three singletons
  have h3A : Disjoint (walkEdges (p3.append s2.reverse)) (walkEdges A) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p3 A (hAB' 3 (by decide)),
       disjoint_walkEdges s2.reverse A hs2A⟩
  have h4A : Disjoint (walkEdges (p4.append s2.reverse)) (walkEdges A) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p4 A (hAB' 4 (by decide)),
       disjoint_walkEdges s2.reverse A hs2A⟩
  have h3B : Disjoint (walkEdges (p3.append s2.reverse)) (walkEdges B) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p3 B (hBB' 3 (by decide)),
       disjoint_walkEdges s2.reverse B hs2B⟩
  have h4B : Disjoint (walkEdges (p4.append s2.reverse)) (walkEdges B) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p4 B (hBB' 4 (by decide)),
       disjoint_walkEdges s2.reverse B hs2B⟩
  have h3Q : Disjoint (walkEdges (p3.append s2.reverse)) (walkEdges Q) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p3 Q (hQB' 3),
       disjoint_walkEdges s2.reverse Q hs2Q⟩
  have h4Q : Disjoint (walkEdges (p4.append s2.reverse)) (walkEdges Q) := by
    rw [walkEdges_append]
    exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges p4 Q (hQB' 4),
       disjoint_walkEdges s2.reverse Q hs2Q⟩
  -- the two joint groups against each other
  have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
  have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
  have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
  have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
  have h53 : s1.edges.Disjoint p3.edges := hfamD 5 3 (by decide)
  have h54 : s1.edges.Disjoint p4.edges := hfamD 5 4 (by decide)
  have s03 : p0.edges.Disjoint (s2.reverse).edges := hs2r 0 (by decide)
  have s13 : p1.edges.Disjoint (s2.reverse).edges := hs2r 1 (by decide)
  have s53 : s1.edges.Disjoint (s2.reverse).edges := hs2r 5 (by decide)
  have g00 : Disjoint (walkEdges (p0.append s1)) (walkEdges (p3.append s2.reverse)) :=
    FivePoint.disjoint_append_append p0 s1 p3 s2.reverse h03 s03 h53 s53
  have g01 : Disjoint (walkEdges (p0.append s1)) (walkEdges (p4.append s2.reverse)) :=
    FivePoint.disjoint_append_append p0 s1 p4 s2.reverse h04 s03 h54 s53
  have g10 : Disjoint (walkEdges (p1.append s1)) (walkEdges (p3.append s2.reverse)) :=
    FivePoint.disjoint_append_append p1 s1 p3 s2.reverse h13 s13 h53 s53
  have g11 : Disjoint (walkEdges (p1.append s1)) (walkEdges (p4.append s2.reverse)) :=
    FivePoint.disjoint_append_append p1 s1 p4 s2.reverse h14 s13 h54 s53
  have hW01 : Disjoint (walkEdges (p0.append s1) ∪ walkEdges (p1.append s1))
      (walkEdges (p3.append s2.reverse) ∪ walkEdges (p4.append s2.reverse)) :=
    disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨g00, g01⟩,
      disjoint_union_right.mpr ⟨g10, g11⟩⟩
  have sub3 : walkEdges (p3.append s2.reverse) ⊆ ω := walkEdges_subset _
  have sub4 : walkEdges (p4.append s2.reverse) ⊆ ω := walkEdges_subset _
  refine ⟨walkEdges (p0.append s1) ∪ walkEdges (p1.append s1),
    walkEdges (p3.append s2.reverse) ∪ walkEdges (p4.append s2.reverse),
    walkEdges A, walkEdges B, walkEdges Q,
    (walkEdges_finite (p0.append s1)).union (walkEdges_finite (p1.append s1)),
    (walkEdges_finite (p3.append s2.reverse)).union (walkEdges_finite (p4.append s2.reverse)),
    walkEdges_finite A, walkEdges_finite B, walkEdges_finite Q,
    union_subset (walkEdges_subset (p0.append s1)) (walkEdges_subset (p1.append s1)),
    union_subset sub3 sub4,
    walkEdges_subset A, walkEdges_subset B, walkEdges_subset Q,
    ⟨conn_mono subset_union_left (mem_conn_walkEdges (p0.append s1)),
      conn_mono subset_union_right (mem_conn_walkEdges (p1.append s1))⟩,
    ⟨conn_mono subset_union_left (mem_conn_walkEdges (p3.append s2.reverse)),
      conn_mono subset_union_right (mem_conn_walkEdges (p4.append s2.reverse))⟩,
    mem_conn_walkEdges A, mem_conn_walkEdges B, mem_conn_walkEdges Q,
    hW01, disjoint_union_left.mpr ⟨h0A, h1A⟩, disjoint_union_left.mpr ⟨h0B, h1B⟩,
    disjoint_union_left.mpr ⟨h0Q, h1Q⟩, disjoint_union_left.mpr ⟨h3A, h4A⟩,
    disjoint_union_left.mpr ⟨h3B, h4B⟩, disjoint_union_left.mpr ⟨h3Q, h4Q⟩,
    disjoint_walkEdges A B hAB, disjoint_walkEdges A Q hAQ, disjoint_walkEdges B Q hBQ⟩

end PercLib.CriticalLRP.TreeExpansion.SixPoint
