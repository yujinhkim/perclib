/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Fourteen seven-group BK bounds and exact diagram evaluations for the
`p = 5`, `k = 1` mixed fifth moment.  Definitions are in `Basic`; the
split and cover arguments are in `Split` and `Cover`.

The scoped linter exemptions below are required by the reviewed proof and
must not be removed globally.  Integrated from Ultramath `smwprafq1`
member `m1` at base revision `5c25062c071ed99bd44904ceb185d8dba8f9093f`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Basic
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Split
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Perm
open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

set_option linter.unusedTactic false
variable {V : Type*}

@[expose] public section

/-! ## Pointwise seven-group bounds -/
theorem slotU_le [Countable V] (π : Sym2 V → unitInterval) (j : Fin 7) (b0 b1 b2 b3 b4 t : V) :
    law π (⋃ c, ⋃ u, ⋃ v, ⋃ w, {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t j c u v w}) ≤
      slotU π j b0 b1 b2 b3 b4 t := by
  fin_cases j
  · -- j = 0
    classical
    simp only [slotU]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 0 c u v w}) ⊆
        ⋃ u, ⋃ v, ⋃ w, SevenGroupEvent (conn b0 u ∩ conn t u) (conn b1 u) (conn b2 v) (conn b3 w) (conn b4 w) (conn u v) (conn v w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨u, v, w,
        sevenGroup_of_six_precise A Q B p1 p2 p3 p4 s1 s2
          ⟨⟨hA1, hQ1, hB1⟩,
            ⟨hA2, hQ2, hB2⟩,
            ⟨hA3, hQ3, hB3⟩,
            ⟨hA4, hQ4, hB4⟩,
            ⟨hA5, hQ5, hB5⟩,
            ⟨hA6, hQ6, hB6⟩, True.intro⟩
          ⟨h12, h13, h14, h15, h16, h23, h24, h25, h26, h34, h35, h36, h45, h46, h56⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ v, ⋃ w,
      SevenGroupEvent (conn b0 u ∩ conn t u) (conn b1 u) (conn b2 v) (conn b3 w) (conn b4 w) (conn u v) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun u => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ w,
      SevenGroupEvent (conn b0 u ∩ conn t u) (conn b1 u) (conn b2 v) (conn b3 w) (conn b4 w) (conn u v) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun v => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V =>
      SevenGroupEvent (conn b0 u ∩ conn t u) (conn b1 u) (conn b2 v) (conn b3 w) (conn b4 w) (conn u v) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b0 u ∩ conn t u)) (A₁ := (conn b1 u)) (A₂ := (conn b2 v)) (A₃ := (conn b3 w)) (A₄ := (conn b4 w)) (A₅ := (conn u v)) (A₆ := (conn v w))
      (isUpperSet_inter_conn b0 t u) (isIncreasing_connects b1 u)
      (isIncreasing_connects b2 v) (isIncreasing_connects b3 w) (isIncreasing_connects b4 w)
      (isIncreasing_connects u v) (isIncreasing_connects v w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 1
    classical
    simp only [slotU]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 1 c u v w}) ⊆
        ⋃ v, ⋃ c, ⋃ w, SevenGroupEvent (conn b0 v ∩ conn c v) (conn b1 c) (conn t c) (conn b2 v) (conn b3 w) (conn b4 w) (conn v w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨v, c, w,
        sevenGroup_of_six_precise p0 B s1 A Q p2 p3 p4 s2
          ⟨⟨(hA0).symm, (hAB).symm, (hA5).symm⟩,
            ⟨(hQ0).symm, hBQ, (hQ5).symm⟩,
            ⟨h02, hB2, (h25).symm⟩,
            ⟨h03, hB3, (h35).symm⟩,
            ⟨h04, hB4, (h45).symm⟩,
            ⟨h06, hB6, h56⟩, True.intro⟩
          ⟨hAQ, hA2, hA3, hA4, hA6, hQ2, hQ3, hQ4, hQ6, h23, h24, h26, h34, h36, h46⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ c, ⋃ w,
      SevenGroupEvent (conn b0 v ∩ conn c v) (conn b1 c) (conn t c) (conn b2 v) (conn b3 w) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun v => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ w,
      SevenGroupEvent (conn b0 v ∩ conn c v) (conn b1 c) (conn t c) (conn b2 v) (conn b3 w) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V =>
      SevenGroupEvent (conn b0 v ∩ conn c v) (conn b1 c) (conn t c) (conn b2 v) (conn b3 w) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b0 v ∩ conn c v)) (A₁ := (conn b1 c)) (A₂ := (conn t c)) (A₃ := (conn b2 v)) (A₄ := (conn b3 w)) (A₅ := (conn b4 w)) (A₆ := (conn v w))
      (isUpperSet_inter_conn b0 c v) (isIncreasing_connects b1 c)
      (isIncreasing_connects t c) (isIncreasing_connects b2 v) (isIncreasing_connects b3 w)
      (isIncreasing_connects b4 w) (isIncreasing_connects v w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 2
    classical
    simp only [slotU]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 2 c u v w}) ⊆
        ⋃ v, ⋃ c, ⋃ w, SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 c) (conn c v) (conn t c) (conn b3 w) (conn b4 w) (conn v w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨v, c, w,
        sevenGroup_of_six_precise p0 p1 s1 A B Q p3 p4 s2
          ⟨⟨(hA0).symm, (hA1).symm, (hA5).symm⟩,
            ⟨(hB0).symm, (hB1).symm, (hB5).symm⟩,
            ⟨(hQ0).symm, (hQ1).symm, (hQ5).symm⟩,
            ⟨h03, h13, (h35).symm⟩,
            ⟨h04, h14, (h45).symm⟩,
            ⟨h06, h16, h56⟩, True.intro⟩
          ⟨hAB, hAQ, hA3, hA4, hA6, hBQ, hB3, hB4, hB6, hQ3, hQ4, hQ6, h34, h36, h46⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ c, ⋃ w,
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 c) (conn c v) (conn t c) (conn b3 w) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun v => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ w,
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 c) (conn c v) (conn t c) (conn b3 w) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V =>
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 c) (conn c v) (conn t c) (conn b3 w) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b0 v ∩ conn b1 v)) (A₁ := (conn b2 c)) (A₂ := (conn c v)) (A₃ := (conn t c)) (A₄ := (conn b3 w)) (A₅ := (conn b4 w)) (A₆ := (conn v w))
      (isUpperSet_inter_conn b0 b1 v) (isIncreasing_connects b2 c)
      (isIncreasing_connects c v) (isIncreasing_connects t c) (isIncreasing_connects b3 w)
      (isIncreasing_connects b4 w) (isIncreasing_connects v w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 3
    classical
    simp only [slotU]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 3 c u v w}) ⊆
        ⋃ v, ⋃ w, ⋃ c, SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 c) (conn c w) (conn t c) (conn b4 w) (conn v w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨v, w, c,
        sevenGroup_of_six_precise p0 p1 s1 p2 A B Q p4 s2
          ⟨⟨h02, h12, (h25).symm⟩,
            ⟨(hA0).symm, (hA1).symm, (hA5).symm⟩,
            ⟨(hB0).symm, (hB1).symm, (hB5).symm⟩,
            ⟨(hQ0).symm, (hQ1).symm, (hQ5).symm⟩,
            ⟨h04, h14, (h45).symm⟩,
            ⟨h06, h16, h56⟩, True.intro⟩
          ⟨(hA2).symm, (hB2).symm, (hQ2).symm, h24, h26, hAB, hAQ, hA4, hA6, hBQ, hB4, hB6, hQ4, hQ6, h46⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ w, ⋃ c,
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 c) (conn c w) (conn t c) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun v => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V => ⋃ c,
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 c) (conn c w) (conn t c) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V =>
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 c) (conn c w) (conn t c) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b0 v ∩ conn b1 v)) (A₁ := (conn b2 v)) (A₂ := (conn b3 c)) (A₃ := (conn c w)) (A₄ := (conn t c)) (A₅ := (conn b4 w)) (A₆ := (conn v w))
      (isUpperSet_inter_conn b0 b1 v) (isIncreasing_connects b2 v)
      (isIncreasing_connects b3 c) (isIncreasing_connects c w) (isIncreasing_connects t c)
      (isIncreasing_connects b4 w) (isIncreasing_connects v w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 4
    classical
    simp only [slotU]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 4 c u v w}) ⊆
        ⋃ v, ⋃ w, ⋃ c, SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 w) (conn b4 c) (conn c w) (conn t c) (conn v w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨v, w, c,
        sevenGroup_of_six_precise p0 p1 s1 p2 p3 A B Q s2
          ⟨⟨h02, h12, (h25).symm⟩,
            ⟨h03, h13, (h35).symm⟩,
            ⟨(hA0).symm, (hA1).symm, (hA5).symm⟩,
            ⟨(hB0).symm, (hB1).symm, (hB5).symm⟩,
            ⟨(hQ0).symm, (hQ1).symm, (hQ5).symm⟩,
            ⟨h06, h16, h56⟩, True.intro⟩
          ⟨h23, (hA2).symm, (hB2).symm, (hQ2).symm, h26, (hA3).symm, (hB3).symm, (hQ3).symm, h36, hAB, hAQ, hA6, hBQ, hB6, hQ6⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ w, ⋃ c,
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 w) (conn b4 c) (conn c w) (conn t c) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun v => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V => ⋃ c,
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 w) (conn b4 c) (conn c w) (conn t c) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V =>
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 w) (conn b4 c) (conn c w) (conn t c) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b0 v ∩ conn b1 v)) (A₁ := (conn b2 v)) (A₂ := (conn b3 w)) (A₃ := (conn b4 c)) (A₄ := (conn c w)) (A₅ := (conn t c)) (A₆ := (conn v w))
      (isUpperSet_inter_conn b0 b1 v) (isIncreasing_connects b2 v)
      (isIncreasing_connects b3 w) (isIncreasing_connects b4 c) (isIncreasing_connects c w)
      (isIncreasing_connects t c) (isIncreasing_connects v w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 5
    classical
    simp only [slotU]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 5 c u v w}) ⊆
        ⋃ c, ⋃ v, ⋃ w, SevenGroupEvent (conn b0 c ∩ conn b1 c) (conn b2 v) (conn b3 w) (conn b4 w) (conn v w) (conn c v) (conn t c) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨c, v, w,
        sevenGroup_of_six_precise p0 p1 A p2 p3 p4 s2 B Q
          ⟨⟨h02, h12, hA2⟩,
            ⟨h03, h13, hA3⟩,
            ⟨h04, h14, hA4⟩,
            ⟨h06, h16, hA6⟩,
            ⟨(hB0).symm, (hB1).symm, hAB⟩,
            ⟨(hQ0).symm, (hQ1).symm, hAQ⟩, True.intro⟩
          ⟨h23, h24, h26, (hB2).symm, (hQ2).symm, h34, h36, (hB3).symm, (hQ3).symm, h46, (hB4).symm, (hQ4).symm, (hB6).symm, (hQ6).symm, hBQ⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ v, ⋃ w,
      SevenGroupEvent (conn b0 c ∩ conn b1 c) (conn b2 v) (conn b3 w) (conn b4 w) (conn v w) (conn c v) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ w,
      SevenGroupEvent (conn b0 c ∩ conn b1 c) (conn b2 v) (conn b3 w) (conn b4 w) (conn v w) (conn c v) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun v => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V =>
      SevenGroupEvent (conn b0 c ∩ conn b1 c) (conn b2 v) (conn b3 w) (conn b4 w) (conn v w) (conn c v) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b0 c ∩ conn b1 c)) (A₁ := (conn b2 v)) (A₂ := (conn b3 w)) (A₃ := (conn b4 w)) (A₄ := (conn v w)) (A₅ := (conn c v)) (A₆ := (conn t c))
      (isUpperSet_inter_conn b0 b1 c) (isIncreasing_connects b2 v)
      (isIncreasing_connects b3 w) (isIncreasing_connects b4 w) (isIncreasing_connects v w)
      (isIncreasing_connects c v) (isIncreasing_connects t c)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 6
    classical
    simp only [slotU]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 6 c u v w}) ⊆
        ⋃ v, ⋃ c, ⋃ w, SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 w) (conn b4 w) (conn v c) (conn c w) (conn t c) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨v, c, w,
        sevenGroup_of_six_precise p0 p1 s1 p2 p3 p4 A B Q
          ⟨⟨h02, h12, (h25).symm⟩,
            ⟨h03, h13, (h35).symm⟩,
            ⟨h04, h14, (h45).symm⟩,
            ⟨(hA0).symm, (hA1).symm, (hA5).symm⟩,
            ⟨(hB0).symm, (hB1).symm, (hB5).symm⟩,
            ⟨(hQ0).symm, (hQ1).symm, (hQ5).symm⟩, True.intro⟩
          ⟨h23, h24, (hA2).symm, (hB2).symm, (hQ2).symm, h34, (hA3).symm, (hB3).symm, (hQ3).symm, (hA4).symm, (hB4).symm, (hQ4).symm, hAB, hAQ, hBQ⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ c, ⋃ w,
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 w) (conn b4 w) (conn v c) (conn c w) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun v => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ w,
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 w) (conn b4 w) (conn v c) (conn c w) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V =>
      SevenGroupEvent (conn b0 v ∩ conn b1 v) (conn b2 v) (conn b3 w) (conn b4 w) (conn v c) (conn c w) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b0 v ∩ conn b1 v)) (A₁ := (conn b2 v)) (A₂ := (conn b3 w)) (A₃ := (conn b4 w)) (A₄ := (conn v c)) (A₅ := (conn c w)) (A₆ := (conn t c))
      (isUpperSet_inter_conn b0 b1 v) (isIncreasing_connects b2 v)
      (isIncreasing_connects b3 w) (isIncreasing_connects b4 w) (isIncreasing_connects v c)
      (isIncreasing_connects c w) (isIncreasing_connects t c)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring

theorem slotV_le [Countable V] (π : Sym2 V → unitInterval) (j : Fin 7) (b0 b1 b2 b3 b4 t : V) :
    law π (⋃ c, ⋃ u, ⋃ v, ⋃ w, {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t j c u v w}) ≤
      slotV π j b0 b1 b2 b3 b4 t := by
  fin_cases j
  · -- j = 0
    classical
    simp only [slotV]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 0 c u v w}) ⊆
        ⋃ w, ⋃ u, ⋃ c, SevenGroupEvent (conn b2 w ∩ conn u w) (conn b1 u) (conn b0 c) (conn c u) (conn t c) (conn b3 w) (conn b4 w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨w, u, c,
        sevenGroup_of_six_precise p2 s1 s2 p1 A B Q p3 p4
          ⟨⟨(h12).symm, (h15).symm, (h16).symm⟩,
            ⟨(hA2).symm, (hA5).symm, (hA6).symm⟩,
            ⟨(hB2).symm, (hB5).symm, (hB6).symm⟩,
            ⟨(hQ2).symm, (hQ5).symm, (hQ6).symm⟩,
            ⟨h23, (h35).symm, (h36).symm⟩,
            ⟨h24, (h45).symm, (h46).symm⟩, True.intro⟩
          ⟨(hA1).symm, (hB1).symm, (hQ1).symm, h13, h14, hAB, hAQ, hA3, hA4, hBQ, hB3, hB4, hQ3, hQ4, h34⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V => ⋃ u, ⋃ c,
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b1 u) (conn b0 c) (conn c u) (conn t c) (conn b3 w) (conn b4 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ c,
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b1 u) (conn b0 c) (conn c u) (conn t c) (conn b3 w) (conn b4 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun u => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V =>
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b1 u) (conn b0 c) (conn c u) (conn t c) (conn b3 w) (conn b4 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b2 w ∩ conn u w)) (A₁ := (conn b1 u)) (A₂ := (conn b0 c)) (A₃ := (conn c u)) (A₄ := (conn t c)) (A₅ := (conn b3 w)) (A₆ := (conn b4 w))
      (isUpperSet_inter_conn b2 u w) (isIncreasing_connects b1 u)
      (isIncreasing_connects b0 c) (isIncreasing_connects c u) (isIncreasing_connects t c)
      (isIncreasing_connects b3 w) (isIncreasing_connects b4 w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 1
    classical
    simp only [slotV]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 1 c u v w}) ⊆
        ⋃ w, ⋃ u, ⋃ c, SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 c) (conn c u) (conn t c) (conn b3 w) (conn b4 w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨w, u, c,
        sevenGroup_of_six_precise p2 s1 s2 p0 A B Q p3 p4
          ⟨⟨(h02).symm, (h05).symm, (h06).symm⟩,
            ⟨(hA2).symm, (hA5).symm, (hA6).symm⟩,
            ⟨(hB2).symm, (hB5).symm, (hB6).symm⟩,
            ⟨(hQ2).symm, (hQ5).symm, (hQ6).symm⟩,
            ⟨h23, (h35).symm, (h36).symm⟩,
            ⟨h24, (h45).symm, (h46).symm⟩, True.intro⟩
          ⟨(hA0).symm, (hB0).symm, (hQ0).symm, h03, h04, hAB, hAQ, hA3, hA4, hBQ, hB3, hB4, hQ3, hQ4, h34⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V => ⋃ u, ⋃ c,
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 c) (conn c u) (conn t c) (conn b3 w) (conn b4 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ c,
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 c) (conn c u) (conn t c) (conn b3 w) (conn b4 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun u => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V =>
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 c) (conn c u) (conn t c) (conn b3 w) (conn b4 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b2 w ∩ conn u w)) (A₁ := (conn b0 u)) (A₂ := (conn b1 c)) (A₃ := (conn c u)) (A₄ := (conn t c)) (A₅ := (conn b3 w)) (A₆ := (conn b4 w))
      (isUpperSet_inter_conn b2 u w) (isIncreasing_connects b0 u)
      (isIncreasing_connects b1 c) (isIncreasing_connects c u) (isIncreasing_connects t c)
      (isIncreasing_connects b3 w) (isIncreasing_connects b4 w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 2
    classical
    simp only [slotV]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 2 c u v w}) ⊆
        ⋃ v, ⋃ u, ⋃ w, SevenGroupEvent (conn b2 v ∩ conn t v) (conn b0 u) (conn b1 u) (conn u v) (conn b3 w) (conn b4 w) (conn v w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨v, u, w,
        sevenGroup_of_six_precise A Q B p0 p1 s1 p3 p4 s2
          ⟨⟨hA0, hQ0, hB0⟩,
            ⟨hA1, hQ1, hB1⟩,
            ⟨hA5, hQ5, hB5⟩,
            ⟨hA3, hQ3, hB3⟩,
            ⟨hA4, hQ4, hB4⟩,
            ⟨hA6, hQ6, hB6⟩, True.intro⟩
          ⟨h01, h05, h03, h04, h06, h15, h13, h14, h16, (h35).symm, (h45).symm, h56, h34, h36, h46⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ u, ⋃ w,
      SevenGroupEvent (conn b2 v ∩ conn t v) (conn b0 u) (conn b1 u) (conn u v) (conn b3 w) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun v => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ w,
      SevenGroupEvent (conn b2 v ∩ conn t v) (conn b0 u) (conn b1 u) (conn u v) (conn b3 w) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun u => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V =>
      SevenGroupEvent (conn b2 v ∩ conn t v) (conn b0 u) (conn b1 u) (conn u v) (conn b3 w) (conn b4 w) (conn v w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b2 v ∩ conn t v)) (A₁ := (conn b0 u)) (A₂ := (conn b1 u)) (A₃ := (conn u v)) (A₄ := (conn b3 w)) (A₅ := (conn b4 w)) (A₆ := (conn v w))
      (isUpperSet_inter_conn b2 t v) (isIncreasing_connects b0 u)
      (isIncreasing_connects b1 u) (isIncreasing_connects u v) (isIncreasing_connects b3 w)
      (isIncreasing_connects b4 w) (isIncreasing_connects v w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 3
    classical
    simp only [slotV]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 3 c u v w}) ⊆
        ⋃ w, ⋃ u, ⋃ c, SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 u) (conn b3 c) (conn c w) (conn t c) (conn b4 w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨w, u, c,
        sevenGroup_of_six_precise p2 s1 s2 p0 p1 A B Q p4
          ⟨⟨(h02).symm, (h05).symm, (h06).symm⟩,
            ⟨(h12).symm, (h15).symm, (h16).symm⟩,
            ⟨(hA2).symm, (hA5).symm, (hA6).symm⟩,
            ⟨(hB2).symm, (hB5).symm, (hB6).symm⟩,
            ⟨(hQ2).symm, (hQ5).symm, (hQ6).symm⟩,
            ⟨h24, (h45).symm, (h46).symm⟩, True.intro⟩
          ⟨h01, (hA0).symm, (hB0).symm, (hQ0).symm, h04, (hA1).symm, (hB1).symm, (hQ1).symm, h14, hAB, hAQ, hA4, hBQ, hB4, hQ4⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V => ⋃ u, ⋃ c,
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 u) (conn b3 c) (conn c w) (conn t c) (conn b4 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ c,
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 u) (conn b3 c) (conn c w) (conn t c) (conn b4 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun u => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V =>
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 u) (conn b3 c) (conn c w) (conn t c) (conn b4 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b2 w ∩ conn u w)) (A₁ := (conn b0 u)) (A₂ := (conn b1 u)) (A₃ := (conn b3 c)) (A₄ := (conn c w)) (A₅ := (conn t c)) (A₆ := (conn b4 w))
      (isUpperSet_inter_conn b2 u w) (isIncreasing_connects b0 u)
      (isIncreasing_connects b1 u) (isIncreasing_connects b3 c) (isIncreasing_connects c w)
      (isIncreasing_connects t c) (isIncreasing_connects b4 w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 4
    classical
    simp only [slotV]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 4 c u v w}) ⊆
        ⋃ w, ⋃ u, ⋃ c, SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 u) (conn b4 c) (conn c w) (conn t c) (conn b3 w) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨w, u, c,
        sevenGroup_of_six_precise p2 s1 s2 p0 p1 A B Q p3
          ⟨⟨(h02).symm, (h05).symm, (h06).symm⟩,
            ⟨(h12).symm, (h15).symm, (h16).symm⟩,
            ⟨(hA2).symm, (hA5).symm, (hA6).symm⟩,
            ⟨(hB2).symm, (hB5).symm, (hB6).symm⟩,
            ⟨(hQ2).symm, (hQ5).symm, (hQ6).symm⟩,
            ⟨h23, (h35).symm, (h36).symm⟩, True.intro⟩
          ⟨h01, (hA0).symm, (hB0).symm, (hQ0).symm, h03, (hA1).symm, (hB1).symm, (hQ1).symm, h13, hAB, hAQ, hA3, hBQ, hB3, hQ3⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V => ⋃ u, ⋃ c,
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 u) (conn b4 c) (conn c w) (conn t c) (conn b3 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ c,
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 u) (conn b4 c) (conn c w) (conn t c) (conn b3 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun u => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V =>
      SevenGroupEvent (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 u) (conn b4 c) (conn c w) (conn t c) (conn b3 w))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b2 w ∩ conn u w)) (A₁ := (conn b0 u)) (A₂ := (conn b1 u)) (A₃ := (conn b4 c)) (A₄ := (conn c w)) (A₅ := (conn t c)) (A₆ := (conn b3 w))
      (isUpperSet_inter_conn b2 u w) (isIncreasing_connects b0 u)
      (isIncreasing_connects b1 u) (isIncreasing_connects b4 c) (isIncreasing_connects c w)
      (isIncreasing_connects t c) (isIncreasing_connects b3 w)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 5
    classical
    simp only [slotV]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 5 c u v w}) ⊆
        ⋃ w, ⋃ c, ⋃ u, SevenGroupEvent (conn b2 w ∩ conn c w) (conn b0 u) (conn b1 u) (conn u c) (conn b3 w) (conn b4 w) (conn t c) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hA6 : A.edges.Disjoint s2.edges := hA 6 (by decide)
      have hB6 : B.edges.Disjoint s2.edges := hB 6 (by decide)
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨w, c, u,
        sevenGroup_of_six_precise p2 B s2 p0 p1 A p3 p4 Q
          ⟨⟨(h02).symm, hB0, (h06).symm⟩,
            ⟨(h12).symm, hB1, (h16).symm⟩,
            ⟨(hA2).symm, (hAB).symm, (hA6).symm⟩,
            ⟨h23, hB3, (h36).symm⟩,
            ⟨h24, hB4, (h46).symm⟩,
            ⟨(hQ2).symm, hBQ, (hQ6).symm⟩, True.intro⟩
          ⟨h01, (hA0).symm, h03, h04, (hQ0).symm, (hA1).symm, h13, h14, (hQ1).symm, hA3, hA4, hAQ, h34, (hQ3).symm, (hQ4).symm⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V => ⋃ c, ⋃ u,
      SevenGroupEvent (conn b2 w ∩ conn c w) (conn b0 u) (conn b1 u) (conn u c) (conn b3 w) (conn b4 w) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ u,
      SevenGroupEvent (conn b2 w ∩ conn c w) (conn b0 u) (conn b1 u) (conn u c) (conn b3 w) (conn b4 w) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun u : V =>
      SevenGroupEvent (conn b2 w ∩ conn c w) (conn b0 u) (conn b1 u) (conn u c) (conn b3 w) (conn b4 w) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun u => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b2 w ∩ conn c w)) (A₁ := (conn b0 u)) (A₂ := (conn b1 u)) (A₃ := (conn u c)) (A₄ := (conn b3 w)) (A₅ := (conn b4 w)) (A₆ := (conn t c))
      (isUpperSet_inter_conn b2 c w) (isIncreasing_connects b0 u)
      (isIncreasing_connects b1 u) (isIncreasing_connects u c) (isIncreasing_connects b3 w)
      (isIncreasing_connects b4 w) (isIncreasing_connects t c)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring
  · -- j = 6
    classical
    simp only [slotV]
    have hsub : (⋃ c, ⋃ u, ⋃ v, ⋃ w,
        {ω | ShapeEv (openGraph ω) b0 b1 b2 b3 b4 t 6 c u v w}) ⊆
        ⋃ c, ⋃ u, ⋃ w, SevenGroupEvent (conn b2 c ∩ conn u c) (conn b0 u) (conn b1 u) (conn c w) (conn b3 w) (conn b4 w) (conn t c) := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨c, u, v, w, hw⟩ := hω
      obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, hsplit, hfamN, hfamD, hAn, hBn, hQn,
        hAB, hA, hB, hQ, hAQ, hBQ, hcj⟩ := combSystem_nine hw
      have h01 : p0.edges.Disjoint p1.edges := hfamD 0 1 (by decide)
      have h02 : p0.edges.Disjoint p2.edges := hfamD 0 2 (by decide)
      have h03 : p0.edges.Disjoint p3.edges := hfamD 0 3 (by decide)
      have h04 : p0.edges.Disjoint p4.edges := hfamD 0 4 (by decide)
      have h05 : p0.edges.Disjoint s1.edges := hfamD 0 5 (by decide)
      have h06 : p0.edges.Disjoint s2.edges := hfamD 0 6 (by decide)
      have h12 : p1.edges.Disjoint p2.edges := hfamD 1 2 (by decide)
      have h13 : p1.edges.Disjoint p3.edges := hfamD 1 3 (by decide)
      have h14 : p1.edges.Disjoint p4.edges := hfamD 1 4 (by decide)
      have h15 : p1.edges.Disjoint s1.edges := hfamD 1 5 (by decide)
      have h16 : p1.edges.Disjoint s2.edges := hfamD 1 6 (by decide)
      have h23 : p2.edges.Disjoint p3.edges := hfamD 2 3 (by decide)
      have h24 : p2.edges.Disjoint p4.edges := hfamD 2 4 (by decide)
      have h25 : p2.edges.Disjoint s1.edges := hfamD 2 5 (by decide)
      have h26 : p2.edges.Disjoint s2.edges := hfamD 2 6 (by decide)
      have h34 : p3.edges.Disjoint p4.edges := hfamD 3 4 (by decide)
      have h35 : p3.edges.Disjoint s1.edges := hfamD 3 5 (by decide)
      have h36 : p3.edges.Disjoint s2.edges := hfamD 3 6 (by decide)
      have h45 : p4.edges.Disjoint s1.edges := hfamD 4 5 (by decide)
      have h46 : p4.edges.Disjoint s2.edges := hfamD 4 6 (by decide)
      have h56 : s1.edges.Disjoint s2.edges := hfamD 5 6 (by decide)
      have hA0 : A.edges.Disjoint p0.edges := hA 0 (by decide)
      have hB0 : B.edges.Disjoint p0.edges := hB 0 (by decide)
      have hQ0 : Q.edges.Disjoint p0.edges := hQ 0
      have hA1 : A.edges.Disjoint p1.edges := hA 1 (by decide)
      have hB1 : B.edges.Disjoint p1.edges := hB 1 (by decide)
      have hQ1 : Q.edges.Disjoint p1.edges := hQ 1
      have hA2 : A.edges.Disjoint p2.edges := hA 2 (by decide)
      have hB2 : B.edges.Disjoint p2.edges := hB 2 (by decide)
      have hQ2 : Q.edges.Disjoint p2.edges := hQ 2
      have hA3 : A.edges.Disjoint p3.edges := hA 3 (by decide)
      have hB3 : B.edges.Disjoint p3.edges := hB 3 (by decide)
      have hQ3 : Q.edges.Disjoint p3.edges := hQ 3
      have hA4 : A.edges.Disjoint p4.edges := hA 4 (by decide)
      have hB4 : B.edges.Disjoint p4.edges := hB 4 (by decide)
      have hQ4 : Q.edges.Disjoint p4.edges := hQ 4
      have hA5 : A.edges.Disjoint s1.edges := hA 5 (by decide)
      have hB5 : B.edges.Disjoint s1.edges := hB 5 (by decide)
      have hQ5 : Q.edges.Disjoint s1.edges := hQ 5
      have hQ6 : Q.edges.Disjoint s2.edges := hQ 6
      exact ⟨c, u, w,
        sevenGroup_of_six_precise p2 s1 A p0 p1 B p3 p4 Q
          ⟨⟨(h02).symm, (h05).symm, hA0⟩,
            ⟨(h12).symm, (h15).symm, hA1⟩,
            ⟨(hB2).symm, (hB5).symm, hAB⟩,
            ⟨h23, (h35).symm, hA3⟩,
            ⟨h24, (h45).symm, hA4⟩,
            ⟨(hQ2).symm, (hQ5).symm, hAQ⟩, True.intro⟩
          ⟨h01, (hB0).symm, h03, h04, (hQ0).symm, (hB1).symm, h13, h14, (hQ1).symm, hB3, hB4, hBQ, h34, (hQ3).symm, (hQ4).symm⟩⟩
    refine (measure_mono hsub).trans ?_
    refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ u, ⋃ w,
      SevenGroupEvent (conn b2 c ∩ conn u c) (conn b0 u) (conn b1 u) (conn c w) (conn b3 w) (conn b4 w) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun c => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ w,
      SevenGroupEvent (conn b2 c ∩ conn u c) (conn b0 u) (conn b1 u) (conn c w) (conn b3 w) (conn b4 w) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun u => ?_
    refine (measure_iUnion_le (μ := law π) (s := fun w : V =>
      SevenGroupEvent (conn b2 c ∩ conn u c) (conn b0 u) (conn b1 u) (conn c w) (conn b3 w) (conn b4 w) (conn t c))).trans ?_
    refine ENNReal.tsum_le_tsum fun w => ?_
    have hbk := sevenGroup_le (V := V) π
      (A₀ := (conn b2 c ∩ conn u c)) (A₁ := (conn b0 u)) (A₂ := (conn b1 u)) (A₃ := (conn c w)) (A₄ := (conn b3 w)) (A₅ := (conn b4 w)) (A₆ := (conn t c))
      (isUpperSet_inter_conn b2 u c) (isIncreasing_connects b0 u)
      (isIncreasing_connects b1 u) (isIncreasing_connects c w) (isIncreasing_connects b3 w)
      (isIncreasing_connects b4 w) (isIncreasing_connects t c)
    refine hbk.trans_eq ?_
    simp only [jointP, tau]
    try ring

/-! ## Exact evaluation of the slot diagrams -/
set_option linter.unusedSimpArgs false
theorem slotU_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval) (j : Fin 7)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, slotU π j 0 b1 b2 b3 b4 t) = secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := by
  have hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x :=
    fun a => tsum_row_eq (tau π) 0 (tau_hinv π hq) a
  have hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x :=
    fun b => tsum_col_eq (tau π) 0 (tau_comm π) (tau_hinv π hq) b
  fin_cases j
  · simp only [slotU]
    refine (tsum_eight_perm permU0 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p3 p0 * (tau π p4 p2 * (tau π p7 p5 * (tau π p6 p5 * (tau π p0 p2 * tau π p2 p5))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0
  · simp only [slotU]
    refine (tsum_eight_perm permU1 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p2 p1 * (tau π p3 p1 * (tau π p4 p0 * (tau π p7 p5 * (tau π p6 p5 * tau π p0 p5))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0
  · simp only [slotU]
    refine (tsum_eight_perm permU2 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p0 p1 * (tau π p4 p2 * (tau π p2 p1 * (tau π p3 p2 * (tau π p7 p5 * (tau π p6 p5 * tau π p1 p5))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' q : V, ∑' c : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre' π hq 0
  · simp only [slotU]
    refine (tsum_eight_perm permU3 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p0 p1 * (tau π p2 p1 * (tau π p4 p3 * (tau π p1 p3 * (tau π p7 p5 * (tau π p6 p5 * tau π p5 p3))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' q : V, ∑' c : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre' π hq 0
  · simp only [slotU]
    refine (tsum_eight_perm permU4 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p0 p1 * (tau π p2 p1 * (tau π p4 p3 * (tau π p1 p3 * (tau π p7 p5 * (tau π p6 p5 * tau π p5 p3))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' q : V, ∑' c : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre' π hq 0
  · simp only [slotU]
    refine (tsum_eight_perm permU5 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p0 p2 * (tau π p4 p2 * (tau π p3 p0 * (tau π p7 p5 * (tau π p6 p5 * tau π p2 p5))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0
  · simp only [slotU]
    refine (tsum_eight_perm permU6 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      tau π p7 p5 * (tau π p6 p5 * (tau π p3 p5 * (tau π p4 p3 * (tau π p1 p3 * (tau π p2 p1 * jointP π 0 p0 p1))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' q : V, ∑' c : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre' π hq 0

theorem slotV_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval) (j : Fin 7)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, slotV π j b0 b1 0 b3 b4 t) = secondMoment π 0 * (∑' x, tau π 0 x) ^ 6 := by
  have hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x :=
    fun a => tsum_row_eq (tau π) 0 (tau_hinv π hq) a
  have hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π 0 x :=
    fun b => tsum_col_eq (tau π) 0 (tau_comm π) (tau_hinv π hq) b
  fin_cases j
  · simp only [slotV]
    refine (tsum_eight_perm permV0 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p2 p1 * (tau π p3 p1 * (tau π p4 p3 * (tau π p5 p3 * (tau π p7 p0 * tau π p6 p0))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0
  · simp only [slotV]
    refine (tsum_eight_perm permV1 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p2 p1 * (tau π p3 p1 * (tau π p4 p3 * (tau π p5 p3 * (tau π p7 p0 * tau π p6 p0))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0
  · simp only [slotV]
    refine (tsum_eight_perm permV2 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p3 p0 * (tau π p5 p3 * (tau π p4 p3 * (tau π p7 p2 * (tau π p6 p2 * tau π p0 p2))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0
  · simp only [slotV]
    refine (tsum_eight_perm permV3 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p2 p0 * (tau π p3 p0 * (tau π p5 p1 * (tau π p4 p1 * (tau π p7 p2 * tau π p6 p2))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0
  · simp only [slotV]
    refine (tsum_eight_perm permV4 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p2 p0 * (tau π p3 p0 * (tau π p5 p1 * (tau π p4 p1 * (tau π p7 p2 * tau π p6 p2))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0
  · simp only [slotV]
    refine (tsum_eight_perm permV5 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p5 p1 * (tau π p2 p1 * (tau π p4 p2 * (tau π p3 p2 * (tau π p7 p0 * tau π p6 p0))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0
  · simp only [slotV]
    refine (tsum_eight_perm permV6 (H := fun p0 p1 p2 p3 p4 p5 p6 p7 =>
      jointP π 0 p1 p0 * (tau π p0 p2 * (tau π p7 p2 * (tau π p6 p2 * (tau π p5 p0 * (tau π p4 p1 * tau π p3 p1))))))).trans ?_
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hrow, hcol]
    suffices h : (∑' c : V, ∑' q : V, jointP π (0 : V) q c) = secondMoment π 0 by
      rw [h]; ring
    exact tsum_jointP_centre π hq 0


end

end PercLib.CriticalLRP.TreeExpansion.SixPoint
