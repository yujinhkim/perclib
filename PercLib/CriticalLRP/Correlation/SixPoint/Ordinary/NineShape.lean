/-
The per-shape nine-singleton BK event bound for the ordinary (`k = 0`) fifth cluster moment.

`combSystem_nine` splits the selected arm of the six-terminal arm system into nine pairwise
edge-disjoint finite walks; the nine certificate sets are the edge sets of those walks, and the
nine increasing events are the two-point connection events between their endpoints
(`nineConns`).  Nine-singleton BK (`Nine.NineFold`) then bounds the probability of one arm system
by the nine-tau diagram `nineDiag`, with no joint pair and no second-moment factor.

Supplied by Ultramath `smwpv4yqm` member `m1` (direction d3, task direction A).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.NineFold

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Probability
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-! ## Edge-disjointness of the nine walks -/

/-- **The nine walks of `combSystem_nine` are pairwise edge-disjoint.**  This is the list-level
input of nine-singleton BK, derived from the output of `Attachment.Split.combSystem_nine`: the six
unsplit comb arms are pairwise disjoint, the two halves of the split arm are disjoint from each
other, from every other arm and from the new arm, and the new arm is disjoint from every arm. -/
theorem nineWalks_edges_disjoint {G : SimpleGraph V} {b0 b1 b2 b3 b4 t u v w c : V} {j : Fin 7}
    (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
    (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) (Q : G.Walk t c)
    (A : G.Walk (armSrc b0 b1 b2 b3 b4 u v j) c) (B : G.Walk c (armTgt u v w j))
    (hfamD : ∀ i k : Fin 7, i ≠ k → (combFam p0 p1 p2 p3 p4 s1 s2 i).edges.Disjoint
      (combFam p0 p1 p2 p3 p4 s1 s2 k).edges)
    (hAB : A.edges.Disjoint B.edges)
    (hAd : ∀ i : Fin 7, i ≠ j → A.edges.Disjoint (combFam p0 p1 p2 p3 p4 s1 s2 i).edges)
    (hBd : ∀ i : Fin 7, i ≠ j → B.edges.Disjoint (combFam p0 p1 p2 p3 p4 s1 s2 i).edges)
    (hQd : ∀ i : Fin 7, Q.edges.Disjoint (combFam p0 p1 p2 p3 p4 s1 s2 i).edges)
    (hAQ : A.edges.Disjoint Q.edges) (hBQ : B.edges.Disjoint Q.edges) :
    ∀ i m : Fin 9, i ≠ m →
      (nineWalks p0 p1 p2 p3 p4 s1 s2 Q A B i).edges.Disjoint
        (nineWalks p0 p1 p2 p3 p4 s1 s2 Q A B m).edges := by
  have hsix : ∀ m₁ m₂ : Fin 6, m₁ ≠ m₂ →
      (combFam p0 p1 p2 p3 p4 s1 s2 (Fin.succAbove j m₁)).edges.Disjoint
        (combFam p0 p1 p2 p3 p4 s1 s2 (Fin.succAbove j m₂)).edges :=
    fun m₁ m₂ h => hfamD _ _ (fun he => h (Fin.succAbove_right_injective he))
  intro i m him
  fin_cases i <;> fin_cases m <;>
    first
      | exact absurd rfl him
      | exact hsix _ _ (by decide)
      | exact hAB
      | exact hAB.symm
      | exact hAQ
      | exact hAQ.symm
      | exact hBQ
      | exact hBQ.symm
      | exact hAd _ (Fin.succAbove_ne _ _)
      | exact (hAd _ (Fin.succAbove_ne _ _)).symm
      | exact hBd _ (Fin.succAbove_ne _ _)
      | exact (hBd _ (Fin.succAbove_ne _ _)).symm
      | exact hQd _
      | exact (hQd _).symm

/-! ## The per-shape event bound -/

/-- **Nine-singleton BK for one six-terminal arm system.**  The probability of the arm system is
at most the nine-tau diagram `nineDiag` of the split tree.  The nine certificates are the edge sets
of the nine walks; all four internal vertices `c, u, v, w` are still free parameters here. -/
theorem law_combSystem_le_nineDiag [Countable V] (π : Sym2 V → unitInterval) (j : Fin 7)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c j} ≤
      nineDiag π j b0 b1 b2 b3 b4 t u v w c := by
  have hsub : {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c j} ⊆
      NineEvent (nineConns j b0 b1 b2 b3 b4 t u v w c) := by
    rintro ω h
    obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
      hAB, hAd, hBd, hQd, hAQ, hBQ, hcj⟩ := combSystem_nine h
    refine mem_nineEvent_of_witnesses (nineConns j b0 b1 b2 b3 b4 t u v w c)
      (fun i => isUpperSet_conn _ _) (W := fun i => walkEdges (nineWalks p0 p1 p2 p3 p4 s1 s2 Q A B i))
      (fun i => walkEdges_finite _) (fun i => walkEdges_subset _)
      (fun i => mem_conn_walkEdges _) (fun i m him => ?_)
    exact disjoint_walkEdges _ _ (nineWalks_edges_disjoint p0 p1 p2 p3 p4 s1 s2 Q A B
      hfamD hAB hAd hBd hQd hAQ hBQ i m him)
  calc law π {ω | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c j}
      ≤ law π (NineEvent (nineConns j b0 b1 b2 b3 b4 t u v w c)) := measure_mono hsub
    _ ≤ ∏ i : Fin 9, law π (nineConns j b0 b1 b2 b3 b4 t u v w c i) :=
        law_nineEvent_le π _ (fun i => isUpperSet_conn _ _)
    _ = nineDiag π j b0 b1 b2 b3 b4 t u v w c := by
        simp only [nineDiag, nineConns, tau]

/-! ## The nine factors, explicitly -/

section EndsLemmas

variable (j : Fin 7) (b0 b1 b2 b3 b4 t u v w c : V)

@[simp] theorem nineEnds_zero :
    nineEnds j b0 b1 b2 b3 b4 t u v w c 0 = (armSrc b0 b1 b2 b3 b4 u v j, c) := rfl

@[simp] theorem nineEnds_one :
    nineEnds j b0 b1 b2 b3 b4 t u v w c 1 = (c, armTgt u v w j) := rfl

@[simp] theorem nineEnds_two :
    nineEnds j b0 b1 b2 b3 b4 t u v w c 2 =
      (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 0), armTgt u v w (Fin.succAbove j 0)) :=
  rfl

@[simp] theorem nineEnds_three :
    nineEnds j b0 b1 b2 b3 b4 t u v w c 3 =
      (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 1), armTgt u v w (Fin.succAbove j 1)) :=
  rfl

@[simp] theorem nineEnds_four :
    nineEnds j b0 b1 b2 b3 b4 t u v w c 4 =
      (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 2), armTgt u v w (Fin.succAbove j 2)) :=
  rfl

@[simp] theorem nineEnds_five :
    nineEnds j b0 b1 b2 b3 b4 t u v w c 5 =
      (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 3), armTgt u v w (Fin.succAbove j 3)) :=
  rfl

@[simp] theorem nineEnds_six :
    nineEnds j b0 b1 b2 b3 b4 t u v w c 6 =
      (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 4), armTgt u v w (Fin.succAbove j 4)) :=
  rfl

@[simp] theorem nineEnds_seven :
    nineEnds j b0 b1 b2 b3 b4 t u v w c 7 =
      (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j 5), armTgt u v w (Fin.succAbove j 5)) :=
  rfl

@[simp] theorem nineEnds_eight :
    nineEnds j b0 b1 b2 b3 b4 t u v w c 8 = (t, c) := rfl

end EndsLemmas

/-- **Explicit nine-factor form of the diagram.**  `nineDiag` is exactly the product of the nine
named factors: the two halves of the split arm, the six unsplit comb arms (enumerated by
`Fin.succAbove j`), and the new arm `t — c`. -/
theorem nineDiag_eq_explicit (π : Sym2 V → unitInterval) (j : Fin 7)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    nineDiag π j b0 b1 b2 b3 b4 t u v w c =
      (tau π (armSrc b0 b1 b2 b3 b4 u v j) c * tau π c (armTgt u v w j)) *
        ((∏ m : Fin 6, tau π (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j m))
            (armTgt u v w (Fin.succAbove j m))) * tau π t c) := by
  rw [nineDiag, Fin.prod_univ_add (a := 2) (b := 7), Fin.prod_univ_two,
    Fin.prod_univ_castSucc]
  have hP : ∀ m : Fin 6,
      tau π (nineEnds j b0 b1 b2 b3 b4 t u v w c (Fin.natAdd 2 (Fin.castSucc m))).1
        (nineEnds j b0 b1 b2 b3 b4 t u v w c (Fin.natAdd 2 (Fin.castSucc m))).2 =
      tau π (armSrc b0 b1 b2 b3 b4 u v (Fin.succAbove j m))
        (armTgt u v w (Fin.succAbove j m)) := by
    intro m
    fin_cases m <;> rfl
  have h0 : (Fin.castAdd 7 (0 : Fin 2)) = (0 : Fin 9) := rfl
  have h1 : (Fin.castAdd 7 (1 : Fin 2)) = (1 : Fin 9) := rfl
  have h8 : (Fin.natAdd 2 (Fin.last 6)) = (8 : Fin 9) := rfl
  simp only [hP, h0, h1, h8]
  rfl

/-- The explicit nine-factor form of the shape diagram. -/
theorem nineShapeDiag_eq_explicit (π : Sym2 V → unitInterval) (T : Fin 6 → V) (k : Fin 15)
    (j : Fin 7) (c u v w : V) :
    nineShapeDiag π T k j c u v w =
      (tau π (armSrc (T (lift5 (pat k 0))) (T (lift5 (pat k 1))) (T (lift5 (pat k 2)))
          (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) u v j) c *
        tau π c (armTgt u v w j)) *
        ((∏ m : Fin 6, tau π (armSrc (T (lift5 (pat k 0))) (T (lift5 (pat k 1)))
            (T (lift5 (pat k 2))) (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) u v
            (Fin.succAbove j m)) (armTgt u v w (Fin.succAbove j m))) * tau π (T 5) c) :=
  nineDiag_eq_explicit π j (T (lift5 (pat k 0))) (T (lift5 (pat k 1)))
    (T (lift5 (pat k 2))) (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) (T 5) u v w c

/-- **The chunk as a sum of explicit nine-factor products.**  This is the form direction B can
evaluate: the five leaf sums are outside, and inside the four internal sums the diagram is the
product of the nine named factors. -/
theorem nineShapeChunk_eq_explicit (π : Sym2 V → unitInterval) (T : Fin 6 → V) (k : Fin 15)
    (j : Fin 7) :
    nineShapeChunk π T k j =
      ∑' c : V, ∑' u : V, ∑' v : V, ∑' w : V,
        (tau π (armSrc (T (lift5 (pat k 0))) (T (lift5 (pat k 1))) (T (lift5 (pat k 2)))
            (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) u v j) c *
          tau π c (armTgt u v w j)) *
          ((∏ m : Fin 6, tau π (armSrc (T (lift5 (pat k 0))) (T (lift5 (pat k 1)))
              (T (lift5 (pat k 2))) (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) u v
              (Fin.succAbove j m)) (armTgt u v w (Fin.succAbove j m))) * tau π (T 5) c) := by
  refine tsum_congr fun c => tsum_congr fun u =>
    tsum_congr fun v => tsum_congr fun w => ?_
  exact nineShapeDiag_eq_explicit π T k j c u v w

/-- **The nine-tau bound in shape form.**  For the `k`-th pattern the four internal vertices
`c, u, v, w` are summed out *inside* the per-shape measure, which is the interface needed by
`Attachment.Assembly.sixPoint_le_sixShapeChunk`. -/
theorem law_sixShape_le_nineShapeDiag [Countable V] (π : Sym2 V → unitInterval)
    (T : Fin 6 → V) (k : Fin 15) (j : Fin 7) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω | SixShape (openGraph ω) k j c u v w T}) ≤
      ∑' c : V, ∑' u : V, ∑' v : V, ∑' w : V, nineShapeDiag π T k j c u v w := by
  refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ u : V, ⋃ v : V, ⋃ w : V,
    {ω | SixShape (openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun c => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ v : V, ⋃ w : V,
    {ω | SixShape (openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun u => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ w : V,
    {ω | SixShape (openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun v => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun w : V =>
    {ω | SixShape (openGraph ω) k j c u v w T})).trans ?_
  exact ENNReal.tsum_le_tsum fun w =>
    law_combSystem_le_nineDiag π j (T (lift5 (pat k 0))) (T (lift5 (pat k 1)))
      (T (lift5 (pat k 2))) (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) (T 5) u v w c

/-- **The chunk form of the per-shape bound.**  Same content as
`law_sixShape_le_nineShapeDiag`, with the four internal sums packaged as `nineShapeChunk`; this is
the input `hP` of the consumer direction with `D k j := nineShapeChunk π T k j`. -/
theorem law_sixShape_le_nineShapeChunk [Countable V] (π : Sym2 V → unitInterval)
    (T : Fin 6 → V) (k : Fin 15) (j : Fin 7) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω | SixShape (openGraph ω) k j c u v w T}) ≤
      nineShapeChunk π T k j :=
  law_sixShape_le_nineShapeDiag π T k j

/-- The chunk bound at the root tuple `(0, y, z, w, q, r)`. -/
theorem law_sixShape_le_nineShapeChunk_root [Countable V] [Zero V]
    (π : Sym2 V → unitInterval) (k : Fin 15) (j : Fin 7) (y z w q r : V) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
        {ω | SixShape (openGraph ω) k j c u v w' ![0, y, z, w, q, r]}) ≤
      nineShapeChunk π ![0, y, z, w, q, r] k j :=
  law_sixShape_le_nineShapeChunk π _ k j

end PercLib.CriticalLRP.TreeExpansion.SixPoint

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.nineWalks_edges_disjoint
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.law_combSystem_le_nineDiag
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.nineEnds_zero
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.nineDiag_eq_explicit
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.nineShapeDiag_eq_explicit
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.nineShapeChunk_eq_explicit
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.law_sixShape_le_nineShapeDiag
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.law_sixShape_le_nineShapeChunk
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.law_sixShape_le_nineShapeChunk_root
