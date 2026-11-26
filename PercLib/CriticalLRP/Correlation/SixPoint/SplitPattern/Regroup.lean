/-
Two-joint/three-single (`k = 2`) regroupings of the `p = 5` six-terminal arm system at split
positions `j = 0`, `j = 5` and `j = 6`.

Swarm `smwxenel0`, member `m2`, direction `I417-TARGET-NORMAL-FORM`.

Production (`SixPoint.combSystem_twoJointThree`) proves the `k = 2` regrouping only at the split
position `j = 2` and only for the star set `S = {u, w}`.  The classification in `Defs.lean`
shows that the nine-edge split tree has three admissible star sets at every one of the seven
split positions, and that the star positions change with `j`.  This file supplies the generic
assembly and the three structurally distinct missing positions:

* `j = 0`: `c` on the arm `b₀ — u`; one star has the landing point `c` as a leaf.
* `j = 5`: `c` on the spine `u — v`; each star uses one half of the split spine.
* `j = 6`: `c` on the spine `v — w`; one star is centred at `c` itself.

The remaining positions `j = 1, 3, 4` are the relabellings `b₀ ↔ b₁` (of `j = 0`) and
`b₃ ↔ b₄` (of `j = 3`, which mirrors `j = 0` across `u ↔ w`); they are not proved here.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitPattern.Defs

/-!
# Generic two-star assembly and three additional split-position certificates

Uses only the finite certificates of `combSystem_nine`. No moment evaluation is asserted here.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern

variable {V : Type*}

/-! ## Reversal and union bookkeeping -/

/-- A walk and its reverse carry the same edge set. -/
theorem walkEdges_reverse [Countable V] {ω : Config V} {a b : V}
    (p : (openGraph ω).Walk a b) : walkEdges p.reverse = walkEdges p := by
  ext e
  simp [walkEdges, SimpleGraph.Walk.edges_reverse]

/-- Disjointness from the three parts of a union. -/
theorem disjoint_union3_left {α : Type*} {A B C D : Set α}
    (hA : Disjoint A D) (hB : Disjoint B D) (hC : Disjoint C D) :
    Disjoint (A ∪ B ∪ C) D := by
  refine Set.disjoint_left.mpr ?_
  intro x hx hd
  rcases hx with (hx | hx) | hx
  · exact (Set.disjoint_left.mp hA) hx hd
  · exact (Set.disjoint_left.mp hB) hx hd
  · exact (Set.disjoint_left.mp hC) hx hd

/-- Disjointness from the three parts of a union, on the right. -/
theorem disjoint_union3_right {α : Type*} {A D E F : Set α}
    (hD : Disjoint A D) (hE : Disjoint A E) (hF : Disjoint A F) :
    Disjoint A (D ∪ E ∪ F) :=
  (disjoint_union3_left hD.symm hE.symm hF.symm).symm

/-- Disjointness of two unions of three sets. -/
theorem disjoint_union3_union3 {α : Type*} {A B C D E F : Set α}
    (hAD : Disjoint A D) (hAE : Disjoint A E) (hAF : Disjoint A F)
    (hBD : Disjoint B D) (hBE : Disjoint B E) (hBF : Disjoint B F)
    (hCD : Disjoint C D) (hCE : Disjoint C E) (hCF : Disjoint C F) :
    Disjoint (A ∪ B ∪ C) (D ∪ E ∪ F) := by
  exact disjoint_union3_left (disjoint_union3_right hAD hAE hAF)
    (disjoint_union3_right hBD hBE hBF) (disjoint_union3_right hCD hCE hCF)

/-! ## One three-star -/

namespace StarCert

variable [Countable V] {ω : Config V}

theorem cert_finite (S : StarCert ω) : S.cert.Finite :=
  (walkEdges_finite (S.legA.append S.spine)).union
    (walkEdges_finite (S.legB.append S.spine))

theorem cert_subset (S : StarCert ω) : S.cert ⊆ ω :=
  union_subset (walkEdges_subset (S.legA.append S.spine))
    (walkEdges_subset (S.legB.append S.spine))

theorem cert_mem (S : StarCert ω) : S.cert ∈ conn S.a S.y ∩ conn S.b S.y :=
  ⟨conn_mono subset_union_left (mem_conn_walkEdges (S.legA.append S.spine)),
   conn_mono subset_union_right (mem_conn_walkEdges (S.legB.append S.spine))⟩

theorem cert_subset_cover (S : StarCert ω) : S.cert ⊆ S.cover := by
  intro e he
  simp only [cert, cover, walkEdges_append, Set.mem_union] at he ⊢
  tauto

end StarCert

/-! ## The two-star assembly -/

/-- **Two three-stars and three two-point factors give the `k = 2` certificate.**  The five
groups are the two star certificates and the three single walks; the hypothesis is that the
three underlying edge-set unions are pairwise disjoint. -/
theorem fiveGroup_of_two_stars [Countable V] {ω : Config V}
    (S₁ S₂ : StarCert ω) (T : Fin 3 → Σ p : V × V, (openGraph ω).Walk p.1 p.2)
    (hd : Disjoint S₁.cover S₂.cover ∧
      (∀ i : Fin 3, Disjoint S₁.cover (walkEdges (T i).2)) ∧
      (∀ i : Fin 3, Disjoint S₂.cover (walkEdges (T i).2)) ∧
      (∀ i k : Fin 3, i ≠ k → Disjoint (walkEdges (T i).2) (walkEdges (T k).2))) :
    ω ∈ TwoJointThreeCert (conn S₁.a S₁.y ∩ conn S₁.b S₁.y)
      (conn S₂.a S₂.y ∩ conn S₂.b S₂.y)
      (conn (T 0).1.1 (T 0).1.2) (conn (T 1).1.1 (T 1).1.2)
      (conn (T 2).1.1 (T 2).1.2) := by
  obtain ⟨hd₁₂, hd₁T, hd₂T, hdTT⟩ := hd
  refine ⟨S₁.cert, S₂.cert, walkEdges (T 0).2, walkEdges (T 1).2, walkEdges (T 2).2,
    S₁.cert_finite, S₂.cert_finite, walkEdges_finite (T 0).2, walkEdges_finite (T 1).2,
    walkEdges_finite (T 2).2, S₁.cert_subset, S₂.cert_subset, walkEdges_subset (T 0).2,
    walkEdges_subset (T 1).2, walkEdges_subset (T 2).2, S₁.cert_mem, S₂.cert_mem,
    mem_conn_walkEdges (T 0).2, mem_conn_walkEdges (T 1).2, mem_conn_walkEdges (T 2).2,
    Set.disjoint_of_subset_left S₁.cert_subset_cover
      (Set.disjoint_of_subset_right S₂.cert_subset_cover hd₁₂),
    Set.disjoint_of_subset_left S₁.cert_subset_cover (hd₁T 0),
    Set.disjoint_of_subset_left S₁.cert_subset_cover (hd₁T 1),
    Set.disjoint_of_subset_left S₁.cert_subset_cover (hd₁T 2),
    Set.disjoint_of_subset_left S₂.cert_subset_cover (hd₂T 0),
    Set.disjoint_of_subset_left S₂.cert_subset_cover (hd₂T 1),
    Set.disjoint_of_subset_left S₂.cert_subset_cover (hd₂T 2),
    hdTT 0 1 (by decide), hdTT 0 2 (by decide), hdTT 1 2 (by decide)⟩



/-! ## Split position `j = 0`: the landing point lies on the arm `b₀ — u` -/

/-- **`k = 2` regrouping at split position `0`.**  The star at `u` has leaves `b₁, c, v`
(splitting into the half `c — u` and the spine `u — v`), the star at `w` has leaves
`b₃, b₄, v`, and the three two-point factors are `b₂ — v`, `b₀ — c` and `t — c`. -/
theorem combSystem_twoJointThree_zero [Countable V] (b0 b1 b2 b3 b4 t u v w c : V) :
    {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 0} ⊆
      TwoJointThreeCert (V := V) (conn b1 v ∩ conn c v) (conn b3 v ∩ conn b4 v)
        (conn b2 v) (conn b0 c) (conn t c) := by
  rintro ω h
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, _hsplit, _hnodup, hfamD, _hAn, _hBn, _hQn,
    hAB, hAi, hBi, hQi, hAQ, hBQ, _hc⟩ := combSystem_nine h
  refine fiveGroup_of_two_stars (ω := ω)
    ⟨u, b1, c, v, p1, B, s1⟩ ⟨w, b3, b4, v, p3, p4, s2.reverse⟩
    ![⟨(b2, v), p2⟩, ⟨(b0, c), A⟩, ⟨(t, c), Q⟩] ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the two stars are disjoint
    refine disjoint_union3_union3
      (disjoint_walkEdges p1 p3 (hfamD 1 3 (by decide)))
      (disjoint_walkEdges p1 p4 (hfamD 1 4 (by decide)))
      ?_ (disjoint_walkEdges B p3 (hBi 3 (by decide)))
      (disjoint_walkEdges B p4 (hBi 4 (by decide))) ?_
      (disjoint_walkEdges s1 p3 (hfamD 5 3 (by decide)))
      (disjoint_walkEdges s1 p4 (hfamD 5 4 (by decide))) ?_
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges p1 s2 (hfamD 1 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges B s2 (hBi 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges s1 s2 (hfamD 5 6 (by decide))
  · -- the first star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p1 p2 (hfamD 1 2 (by decide)))
        (disjoint_walkEdges B p2 (hBi 2 (by decide)))
        (disjoint_walkEdges s1 p2 (hfamD 5 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p1 A (hAi 1 (by decide)).symm)
        (disjoint_walkEdges B A hAB.symm)
        (disjoint_walkEdges s1 A (hAi 5 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p1 (hQi 1)).symm
        (disjoint_walkEdges Q B hBQ.symm).symm
        (disjoint_walkEdges Q s1 (hQi 5)).symm
  · -- the second star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p3 p2 (hfamD 3 2 (by decide)))
        (disjoint_walkEdges p4 p2 (hfamD 4 2 (by decide)))
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 p2 (hfamD 6 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p3 A (hAi 3 (by decide)).symm)
        (disjoint_walkEdges p4 A (hAi 4 (by decide)).symm)
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 A (hAi 6 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p3 (hQi 3)).symm
        (disjoint_walkEdges Q p4 (hQi 4)).symm
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


/-! ## Split position `j = 5`: the landing point lies on the spine `u — v` -/

/-- **`k = 2` regrouping at split position `5`.**  Each star uses one half of the split
spine: the star at `u` has leaves `b₀, b₁, c` and the star at `v` has leaves `b₂, c, w`;
the two-point factors are `b₃ — w`, `b₄ — w` and `t — c`. -/
theorem combSystem_twoJointThree_five [Countable V] (b0 b1 b2 b3 b4 t u v w c : V) :
    {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 5} ⊆
      TwoJointThreeCert (V := V) (conn b0 c ∩ conn b1 c) (conn b2 w ∩ conn c w)
        (conn b3 w) (conn b4 w) (conn t c) := by
  rintro ω h
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, _hsplit, _hnodup, hfamD, _hAn, _hBn, _hQn,
    hAB, hAi, hBi, hQi, hAQ, hBQ, _hc⟩ := combSystem_nine h
  have h12 : Disjoint (walkEdges p0) (walkEdges p2) :=
    disjoint_walkEdges p0 p2 (hfamD 0 2 (by decide))
  have h13 : Disjoint (walkEdges p1) (walkEdges p2) :=
    disjoint_walkEdges p1 p2 (hfamD 1 2 (by decide))
  have h14 : Disjoint (walkEdges A) (walkEdges p2) :=
    disjoint_walkEdges A p2 (hAi 2 (by decide))
  have h15 : Disjoint (walkEdges p0) (walkEdges s2) :=
    disjoint_walkEdges p0 s2 (hfamD 0 6 (by decide))
  have h16 : Disjoint (walkEdges p1) (walkEdges s2) :=
    disjoint_walkEdges p1 s2 (hfamD 1 6 (by decide))
  have h17 : Disjoint (walkEdges A) (walkEdges s2) :=
    disjoint_walkEdges A s2 (hAi 6 (by decide))
  have h21 : Disjoint (walkEdges p0) (walkEdges B) :=
    disjoint_walkEdges p0 B (hBi 0 (by decide)).symm
  have h22 : Disjoint (walkEdges p1) (walkEdges B) :=
    disjoint_walkEdges p1 B (hBi 1 (by decide)).symm
  have h23 : Disjoint (walkEdges A) (walkEdges B) := disjoint_walkEdges A B hAB
  have hQ0 : Disjoint (walkEdges p0) (walkEdges Q) := disjoint_walkEdges Q p0 (hQi 0) |>.symm
  have hQ1 : Disjoint (walkEdges p1) (walkEdges Q) := disjoint_walkEdges Q p1 (hQi 1) |>.symm
  have hQA : Disjoint (walkEdges A) (walkEdges Q) := disjoint_walkEdges A Q hAQ
  have hQB : Disjoint (walkEdges B) (walkEdges Q) := disjoint_walkEdges B Q hBQ
  have hQs2 : Disjoint (walkEdges s2) (walkEdges Q) :=
    (disjoint_walkEdges Q s2 (hQi 6)).symm
  have hB3 : Disjoint (walkEdges B) (walkEdges p3) :=
    disjoint_walkEdges B p3 (hBi 3 (by decide))
  have hB4 : Disjoint (walkEdges B) (walkEdges p4) :=
    disjoint_walkEdges B p4 (hBi 4 (by decide))
  have hs23 : Disjoint (walkEdges s2) (walkEdges p3) :=
    disjoint_walkEdges s2 p3 (hfamD 6 3 (by decide))
  have hs24 : Disjoint (walkEdges s2) (walkEdges p4) :=
    disjoint_walkEdges s2 p4 (hfamD 6 4 (by decide))
  have hp23 : Disjoint (walkEdges p2) (walkEdges p3) :=
    disjoint_walkEdges p2 p3 (hfamD 2 3 (by decide))
  have hp24 : Disjoint (walkEdges p2) (walkEdges p4) :=
    disjoint_walkEdges p2 p4 (hfamD 2 4 (by decide))
  refine fiveGroup_of_two_stars (ω := ω)
    ⟨u, b0, b1, c, p0, p1, A⟩ ⟨v, b2, c, w, p2, B, s2⟩
    ![⟨(b3, w), p3⟩, ⟨(b4, w), p4⟩, ⟨(t, c), Q⟩] ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact disjoint_union3_union3 h12 h21 h15 h13 h22 h16 h14 h23 h17
  · intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p0 p3 (hfamD 0 3 (by decide)))
        (disjoint_walkEdges p1 p3 (hfamD 1 3 (by decide)))
        (disjoint_walkEdges A p3 (hAi 3 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p0 p4 (hfamD 0 4 (by decide)))
        (disjoint_walkEdges p1 p4 (hfamD 1 4 (by decide)))
        (disjoint_walkEdges A p4 (hAi 4 (by decide)))
    · exact disjoint_union3_left hQ0 hQ1 hQA
  · intro i
    fin_cases i
    · exact disjoint_union3_left hp23 hB3 hs23
    · exact disjoint_union3_left hp24 hB4 hs24
    · exact disjoint_union3_left (disjoint_walkEdges Q p2 (hQi 2)).symm hQB hQs2
  · intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact disjoint_walkEdges p3 p4 (hfamD 3 4 (by decide))
    · exact disjoint_walkEdges p3 Q (hQi 3).symm
    · exact disjoint_walkEdges p4 p3 (hfamD 4 3 (by decide))
    · exact absurd rfl hik
    · exact disjoint_walkEdges p4 Q (hQi 4).symm
    · exact disjoint_walkEdges Q p3 (hQi 3)
    · exact disjoint_walkEdges Q p4 (hQi 4)
    · exact absurd rfl hik


/-! ## Split position `j = 6`: the landing point lies on the spine `v — w` -/

/-- **`k = 2` regrouping at split position `6`.**  The star at `u` has leaves `b₀, b₁, v`;
the second star is centred at the landing point `c` with leaves `v, t, w`; the two-point
factors are `b₂ — v`, `b₃ — w` and `b₄ — w`. -/
theorem combSystem_twoJointThree_six [Countable V] (b0 b1 b2 b3 b4 t u v w c : V) :
    {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 6} ⊆
      TwoJointThreeCert (V := V) (conn b0 v ∩ conn b1 v) (conn v w ∩ conn t w)
        (conn b2 v) (conn b3 w) (conn b4 w) := by
  rintro ω h
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, _hsplit, _hnodup, hfamD, _hAn, _hBn, _hQn,
    hAB, hAi, hBi, hQi, hAQ, hBQ, _hc⟩ := combSystem_nine h
  have h0A : Disjoint (walkEdges p0) (walkEdges A) :=
    disjoint_walkEdges p0 A (hAi 0 (by decide)).symm
  have h0Q : Disjoint (walkEdges p0) (walkEdges Q) :=
    disjoint_walkEdges p0 Q (hQi 0).symm
  have h0B : Disjoint (walkEdges p0) (walkEdges B) :=
    disjoint_walkEdges p0 B (hBi 0 (by decide)).symm
  have h1A : Disjoint (walkEdges p1) (walkEdges A) :=
    disjoint_walkEdges p1 A (hAi 1 (by decide)).symm
  have h1Q : Disjoint (walkEdges p1) (walkEdges Q) :=
    disjoint_walkEdges p1 Q (hQi 1).symm
  have h1B : Disjoint (walkEdges p1) (walkEdges B) :=
    disjoint_walkEdges p1 B (hBi 1 (by decide)).symm
  have h5A : Disjoint (walkEdges s1) (walkEdges A) :=
    disjoint_walkEdges s1 A (hAi 5 (by decide)).symm
  have h5Q : Disjoint (walkEdges s1) (walkEdges Q) :=
    disjoint_walkEdges s1 Q (hQi 5).symm
  have h5B : Disjoint (walkEdges s1) (walkEdges B) :=
    disjoint_walkEdges s1 B (hBi 5 (by decide)).symm
  refine fiveGroup_of_two_stars (ω := ω)
    ⟨u, b0, b1, v, p0, p1, s1⟩ ⟨c, v, t, w, A, Q, B⟩
    ![⟨(b2, v), p2⟩, ⟨(b3, w), p3⟩, ⟨(b4, w), p4⟩] ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact disjoint_union3_union3 h0A h0Q h0B h1A h1Q h1B h5A h5Q h5B
  · intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p0 p2 (hfamD 0 2 (by decide)))
        (disjoint_walkEdges p1 p2 (hfamD 1 2 (by decide)))
        (disjoint_walkEdges s1 p2 (hfamD 5 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p0 p3 (hfamD 0 3 (by decide)))
        (disjoint_walkEdges p1 p3 (hfamD 1 3 (by decide)))
        (disjoint_walkEdges s1 p3 (hfamD 5 3 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p0 p4 (hfamD 0 4 (by decide)))
        (disjoint_walkEdges p1 p4 (hfamD 1 4 (by decide)))
        (disjoint_walkEdges s1 p4 (hfamD 5 4 (by decide)))
  · intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges A p2 (hAi 2 (by decide)))
        (disjoint_walkEdges Q p2 (hQi 2)) (disjoint_walkEdges B p2 (hBi 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges A p3 (hAi 3 (by decide)))
        (disjoint_walkEdges Q p3 (hQi 3)) (disjoint_walkEdges B p3 (hBi 3 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges A p4 (hAi 4 (by decide)))
        (disjoint_walkEdges Q p4 (hQi 4)) (disjoint_walkEdges B p4 (hBi 4 (by decide)))
  · intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact disjoint_walkEdges p2 p3 (hfamD 2 3 (by decide))
    · exact disjoint_walkEdges p2 p4 (hfamD 2 4 (by decide))
    · exact disjoint_walkEdges p3 p2 (hfamD 3 2 (by decide))
    · exact absurd rfl hik
    · exact disjoint_walkEdges p3 p4 (hfamD 3 4 (by decide))
    · exact disjoint_walkEdges p4 p2 (hfamD 4 2 (by decide))
    · exact disjoint_walkEdges p4 p3 (hfamD 4 3 (by decide))
    · exact absurd rfl hik

end PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern
