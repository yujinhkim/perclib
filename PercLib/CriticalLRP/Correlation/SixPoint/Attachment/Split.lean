/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Splitting the six-terminal arm system into nine edge-disjoint walks, and the generic
"nine walks to one joint pair plus six singletons" regrouping.
Supplied by Ultramath `smwprafq1` member `m1` (direction d1).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Cover

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-! ## Splitting arm `j` at the landing point -/

/-- **The nine walks of the six-leaf binary tree.**  From the six-terminal arm system we extract
the seven comb arms, the landing point `c` on arm `j`, the two halves `A`, `B` of arm `j`, and the
new arm `Q`.  The nine edge lists are pairwise disjoint and each is a trail; the edge list of arm
`j` is exactly `A ++ B`. -/
theorem combSystem_nine [Countable V] {G : SimpleGraph V} {b0 b1 b2 b3 b4 t u v w c : V} {j : Fin 7}
    (h : CombSystem G b0 b1 b2 b3 b4 t u v w c j) :
    ∃ (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
      (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) (Q : G.Walk t c)
      (A : G.Walk (armSrc b0 b1 b2 b3 b4 u v j) c) (B : G.Walk c (armTgt u v w j)),
      A.edges ++ B.edges = (combFam p0 p1 p2 p3 p4 s1 s2 j).edges ∧
      (∀ i : Fin 7, (combFam p0 p1 p2 p3 p4 s1 s2 i).edges.Nodup) ∧
      (∀ i k : Fin 7, i ≠ k → (combFam p0 p1 p2 p3 p4 s1 s2 i).edges.Disjoint
        (combFam p0 p1 p2 p3 p4 s1 s2 k).edges) ∧
      A.edges.Nodup ∧ B.edges.Nodup ∧ Q.edges.Nodup ∧ A.edges.Disjoint B.edges ∧
      (∀ i : Fin 7, i ≠ j → A.edges.Disjoint (combFam p0 p1 p2 p3 p4 s1 s2 i).edges) ∧
      (∀ i : Fin 7, i ≠ j → B.edges.Disjoint (combFam p0 p1 p2 p3 p4 s1 s2 i).edges) ∧
      (∀ i : Fin 7, Q.edges.Disjoint (combFam p0 p1 p2 p3 p4 s1 s2 i).edges) ∧
      A.edges.Disjoint Q.edges ∧ B.edges.Disjoint Q.edges ∧
      c ∈ (combFam p0 p1 p2 p3 p4 s1 s2 j).support := by
  classical
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, hnd, hcj⟩ := h
  have hnd7 : (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges ++ s1.edges ++
      s2.edges).Nodup := hnd.of_append_left
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, d01, d02, d03, d04, d05, d06, d12, d13, d14, d15,
    d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := nodup_append7_facts hnd7
  have hQn : Q.edges.Nodup := hnd.of_append_right
  have hQall : (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges ++ s1.edges ++ s2.edges).Disjoint Q.edges :=
    List.disjoint_of_nodup_append hnd
  have hr0 : (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges ++ s1.edges).Disjoint Q.edges :=
    (List.disjoint_append_left.mp hQall).1
  have hQ6 : Q.edges.Disjoint s2.edges :=
    (List.disjoint_append_left.mp hQall).2.symm
  have hr1 : (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges).Disjoint Q.edges :=
    (List.disjoint_append_left.mp hr0).1
  have hQ5 : Q.edges.Disjoint s1.edges :=
    (List.disjoint_append_left.mp hr0).2.symm
  have hr2 : (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges).Disjoint Q.edges :=
    (List.disjoint_append_left.mp hr1).1
  have hQ4 : Q.edges.Disjoint p4.edges :=
    (List.disjoint_append_left.mp hr1).2.symm
  have hr3 : (p0.edges ++ p1.edges ++ p2.edges).Disjoint Q.edges :=
    (List.disjoint_append_left.mp hr2).1
  have hQ3 : Q.edges.Disjoint p3.edges :=
    (List.disjoint_append_left.mp hr2).2.symm
  have hr4 : (p0.edges ++ p1.edges).Disjoint Q.edges :=
    (List.disjoint_append_left.mp hr3).1
  have hQ2 : Q.edges.Disjoint p2.edges :=
    (List.disjoint_append_left.mp hr3).2.symm
  have hr5 : (p0.edges).Disjoint Q.edges :=
    (List.disjoint_append_left.mp hr4).1
  have hQ1 : Q.edges.Disjoint p1.edges :=
    (List.disjoint_append_left.mp hr4).2.symm
  have hQ0 : Q.edges.Disjoint p0.edges := hr5.symm
  have hfamN : ∀ i : Fin 7, (combFam p0 p1 p2 p3 p4 s1 s2 i).edges.Nodup := by
    intro i
    fin_cases i
    exacts [n0, n1, n2, n3, n4, n5, n6]
  have hfamD : ∀ i k : Fin 7, i ≠ k → (combFam p0 p1 p2 p3 p4 s1 s2 i).edges.Disjoint
      (combFam p0 p1 p2 p3 p4 s1 s2 k).edges := by
    intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact d01
    · exact d02
    · exact d03
    · exact d04
    · exact d05
    · exact d06
    · exact d01.symm
    · exact absurd rfl hik
    · exact d12
    · exact d13
    · exact d14
    · exact d15
    · exact d16
    · exact d02.symm
    · exact d12.symm
    · exact absurd rfl hik
    · exact d23
    · exact d24
    · exact d25
    · exact d26
    · exact d03.symm
    · exact d13.symm
    · exact d23.symm
    · exact absurd rfl hik
    · exact d34
    · exact d35
    · exact d36
    · exact d04.symm
    · exact d14.symm
    · exact d24.symm
    · exact d34.symm
    · exact absurd rfl hik
    · exact d45
    · exact d46
    · exact d05.symm
    · exact d15.symm
    · exact d25.symm
    · exact d35.symm
    · exact d45.symm
    · exact absurd rfl hik
    · exact d56
    · exact d06.symm
    · exact d16.symm
    · exact d26.symm
    · exact d36.symm
    · exact d46.symm
    · exact d56.symm
    · exact absurd rfl hik
  have hfamQ : ∀ i : Fin 7, Q.edges.Disjoint (combFam p0 p1 p2 p3 p4 s1 s2 i).edges := by
    intro i
    fin_cases i
    exacts [hQ0, hQ1, hQ2, hQ3, hQ4, hQ5, hQ6]
  have hsplit : ((combFam p0 p1 p2 p3 p4 s1 s2 j).takeUntil c hcj).edges ++
      ((combFam p0 p1 p2 p3 p4 s1 s2 j).dropUntil c hcj).edges =
      (combFam p0 p1 p2 p3 p4 s1 s2 j).edges := by
    rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
  have hndsplit : (((combFam p0 p1 p2 p3 p4 s1 s2 j).takeUntil c hcj).edges ++
      ((combFam p0 p1 p2 p3 p4 s1 s2 j).dropUntil c hcj).edges).Nodup := by
    rw [hsplit]; exact hfamN j
  refine ⟨p0, p1, p2, p3, p4, s1, s2, Q, _, _, hsplit, hfamN, hfamD, ?_, ?_, hQn, ?_, ?_, ?_,
    hfamQ, ?_, ?_, hcj⟩
  · exact List.Nodup.of_append_left hndsplit
  · exact List.Nodup.of_append_right hndsplit
  · exact List.disjoint_of_nodup_append hndsplit
  · -- first half versus the other arms
    intro i hi
    exact disjoint_of_subset_left
      (SimpleGraph.Walk.edges_takeUntil_subset_edges _ _) (hfamD j i (Ne.symm hi))
  · -- second half versus the other arms
    intro i hi
    exact disjoint_of_subset_left
      (SimpleGraph.Walk.edges_dropUntil_subset_edges _ _) (hfamD j i (Ne.symm hi))
  · -- first half versus the new arm
    exact disjoint_of_subset_left
      (SimpleGraph.Walk.edges_takeUntil_subset_edges _ _) (hfamQ j).symm
  · -- second half versus the new arm
    exact disjoint_of_subset_left
      (SimpleGraph.Walk.edges_dropUntil_subset_edges _ _) (hfamQ j).symm

/-! ## The generic regrouping: a joint V plus six singletons -/

/-- **Nine walks give a seven-group certificate.**  If the three walks `W₁ : r — x`, `W₂ : z — x`,
`W₃ : x — y` are edge-disjoint from six further walks `S m`, and the `S m` are pairwise
edge-disjoint, then the configuration lies in the certificate event whose joint group is
`conn r y ∩ conn z y` (certified by the two paths through `x`) and whose six singleton groups are
the `S m`. -/
theorem sevenGroup_of_nine [Countable V] {ω : Config V} {r z x y : V}
    (W₁ : (openGraph ω).Walk r x) (W₂ : (openGraph ω).Walk z x) (W₃ : (openGraph ω).Walk x y)
    (S : Fin 6 → Σ p : V × V, (openGraph ω).Walk p.1 p.2)
    (hdV : ∀ m, Disjoint (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) (walkEdges (S m).2))
    (hdS : ∀ m n, m ≠ n → Disjoint (walkEdges (S m).2) (walkEdges (S n).2)) :
    ω ∈ SevenGroupEvent (conn r y ∩ conn z y)
      (conn (S 0).1.1 (S 0).1.2) (conn (S 1).1.1 (S 1).1.2) (conn (S 2).1.1 (S 2).1.2)
      (conn (S 3).1.1 (S 3).1.2) (conn (S 4).1.1 (S 4).1.2) (conn (S 5).1.1 (S 5).1.2) := by
  classical
  have hW₁ : walkEdges (W₁.append W₃) = walkEdges W₁ ∪ walkEdges W₃ := walkEdges_append W₁ W₃
  have hW₂ : walkEdges (W₂.append W₃) = walkEdges W₂ ∪ walkEdges W₃ := walkEdges_append W₂ W₃
  have hsub : (walkEdges (W₁.append W₃) ∪ walkEdges (W₂.append W₃)) ⊆
      (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) := by
    intro e he
    rw [hW₁, hW₂] at he
    simp only [Set.mem_union] at he ⊢
    tauto
  have hd0 : ∀ m, Disjoint (walkEdges (W₁.append W₃) ∪ walkEdges (W₂.append W₃))
      (walkEdges (S m).2) := fun m =>
    Set.disjoint_of_subset_left hsub (hdV m)
  refine ⟨walkEdges (W₁.append W₃) ∪ walkEdges (W₂.append W₃), walkEdges (S 0).2,
    walkEdges (S 1).2, walkEdges (S 2).2, walkEdges (S 3).2, walkEdges (S 4).2,
    walkEdges (S 5).2,
    (walkEdges_finite (W₁.append W₃)).union (walkEdges_finite (W₂.append W₃)),
    walkEdges_finite (S 0).2, walkEdges_finite (S 1).2, walkEdges_finite (S 2).2,
    walkEdges_finite (S 3).2, walkEdges_finite (S 4).2, walkEdges_finite (S 5).2,
    union_subset (walkEdges_subset (W₁.append W₃)) (walkEdges_subset (W₂.append W₃)),
    walkEdges_subset (S 0).2, walkEdges_subset (S 1).2, walkEdges_subset (S 2).2,
    walkEdges_subset (S 3).2, walkEdges_subset (S 4).2, walkEdges_subset (S 5).2,
    ⟨conn_mono subset_union_left (mem_conn_walkEdges (W₁.append W₃)),
      conn_mono subset_union_right (mem_conn_walkEdges (W₂.append W₃))⟩,
    mem_conn_walkEdges (S 0).2, mem_conn_walkEdges (S 1).2, mem_conn_walkEdges (S 2).2,
    mem_conn_walkEdges (S 3).2, mem_conn_walkEdges (S 4).2, mem_conn_walkEdges (S 5).2,
    hd0 0, hd0 1, hd0 2, hd0 3, hd0 4, hd0 5,
    hdS 0 1 (by decide), hdS 0 2 (by decide), hdS 0 3 (by decide), hdS 0 4 (by decide),
    hdS 0 5 (by decide), hdS 1 2 (by decide), hdS 1 3 (by decide), hdS 1 4 (by decide),
    hdS 1 5 (by decide), hdS 2 3 (by decide), hdS 2 4 (by decide), hdS 2 5 (by decide),
    hdS 3 4 (by decide), hdS 3 5 (by decide), hdS 4 5 (by decide)⟩

end PercLib.CriticalLRP.TreeExpansion.SixPoint

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- **Six walks plus a joint pair give the seven-group certificate** (list-level disjointness
input). -/
theorem sevenGroup_of_six [Countable V] {ω : Config V} {r z x y : V}
    (W₁ : (openGraph ω).Walk r x) (W₂ : (openGraph ω).Walk z x) (W₃ : (openGraph ω).Walk x y)
    (S : Fin 6 → Σ p : V × V, (openGraph ω).Walk p.1 p.2)
    (hdV : ∀ m, W₁.edges.Disjoint (S m).2.edges ∧ W₂.edges.Disjoint (S m).2.edges ∧
      W₃.edges.Disjoint (S m).2.edges)
    (hdS : ∀ m n, m ≠ n → (S m).2.edges.Disjoint (S n).2.edges) :
    ω ∈ SevenGroupEvent (conn r y ∩ conn z y)
      (conn (S 0).1.1 (S 0).1.2) (conn (S 1).1.1 (S 1).1.2) (conn (S 2).1.1 (S 2).1.2)
      (conn (S 3).1.1 (S 3).1.2) (conn (S 4).1.1 (S 4).1.2) (conn (S 5).1.1 (S 5).1.2) := by
  classical
  have hdW : ∀ m, Disjoint (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) (walkEdges (S m).2) := by
    intro m
    refine Set.disjoint_left.mpr ?_
    intro e he he'
    rcases he with he | he
    · rcases he with he | he
      · exact (hdV m).1 he (he')
      · exact (hdV m).2.1 he he'
    · exact (hdV m).2.2 he he'
  have hdS' : ∀ m n, m ≠ n → Disjoint (walkEdges (S m).2) (walkEdges (S n).2) :=
    fun m n hmn => disjoint_walkEdges (S m).2 (S n).2 (hdS m n hmn)
  exact sevenGroup_of_nine W₁ W₂ W₃ S hdW hdS'


/-- **Six walks plus a joint pair give the seven-group certificate** (fully explicit form). -/
theorem sevenGroup_of_six_precise [Countable V] {ω : Config V}
    {r z x y a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ a₅ b₅ : V}
    (W₁ : (openGraph ω).Walk r x) (W₂ : (openGraph ω).Walk z x) (W₃ : (openGraph ω).Walk x y)
    (T₀ : (openGraph ω).Walk a₀ b₀) (T₁ : (openGraph ω).Walk a₁ b₁)
    (T₂ : (openGraph ω).Walk a₂ b₂) (T₃ : (openGraph ω).Walk a₃ b₃)
    (T₄ : (openGraph ω).Walk a₄ b₄) (T₅ : (openGraph ω).Walk a₅ b₅)
    (hV : (W₁.edges.Disjoint T₀.edges ∧ W₂.edges.Disjoint T₀.edges ∧ W₃.edges.Disjoint T₀.edges) ∧
      (W₁.edges.Disjoint T₁.edges ∧ W₂.edges.Disjoint T₁.edges ∧ W₃.edges.Disjoint T₁.edges) ∧
      (W₁.edges.Disjoint T₂.edges ∧ W₂.edges.Disjoint T₂.edges ∧ W₃.edges.Disjoint T₂.edges) ∧
      (W₁.edges.Disjoint T₃.edges ∧ W₂.edges.Disjoint T₃.edges ∧ W₃.edges.Disjoint T₃.edges) ∧
      (W₁.edges.Disjoint T₄.edges ∧ W₂.edges.Disjoint T₄.edges ∧ W₃.edges.Disjoint T₄.edges) ∧
      (W₁.edges.Disjoint T₅.edges ∧ W₂.edges.Disjoint T₅.edges ∧ W₃.edges.Disjoint T₅.edges) ∧
      True)
    (hS : T₀.edges.Disjoint T₁.edges ∧ T₀.edges.Disjoint T₂.edges ∧
      T₀.edges.Disjoint T₃.edges ∧ T₀.edges.Disjoint T₄.edges ∧ T₀.edges.Disjoint T₅.edges ∧
      T₁.edges.Disjoint T₂.edges ∧ T₁.edges.Disjoint T₃.edges ∧ T₁.edges.Disjoint T₄.edges ∧
      T₁.edges.Disjoint T₅.edges ∧ T₂.edges.Disjoint T₃.edges ∧ T₂.edges.Disjoint T₄.edges ∧
      T₂.edges.Disjoint T₅.edges ∧ T₃.edges.Disjoint T₄.edges ∧ T₃.edges.Disjoint T₅.edges ∧
      T₄.edges.Disjoint T₅.edges) :
    ω ∈ SevenGroupEvent (conn r y ∩ conn z y) (conn a₀ b₀) (conn a₁ b₁) (conn a₂ b₂)
      (conn a₃ b₃) (conn a₄ b₄) (conn a₅ b₅) := by
  classical
  obtain ⟨⟨v0a, v0b, v0c⟩, ⟨v1a, v1b, v1c⟩, ⟨v2a, v2b, v2c⟩, ⟨v3a, v3b, v3c⟩,
    ⟨v4a, v4b, v4c⟩, ⟨v5a, v5b, v5c⟩, -⟩ := hV
  obtain ⟨s01, s02, s03, s04, s05, s12, s13, s14, s15, s23, s24, s25, s34, s35, s45⟩ := hS
  have hT₀ : Disjoint (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) (walkEdges T₀) :=
    Set.disjoint_left.mpr fun e he he' => by
      rcases he with he | he
      · rcases he with he | he
        · exact v0a he he'
        · exact v0b he he'
      · exact v0c he he'
  have hT₁ : Disjoint (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) (walkEdges T₁) :=
    Set.disjoint_left.mpr fun e he he' => by
      rcases he with he | he
      · rcases he with he | he
        · exact v1a he he'
        · exact v1b he he'
      · exact v1c he he'
  have hT₂ : Disjoint (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) (walkEdges T₂) :=
    Set.disjoint_left.mpr fun e he he' => by
      rcases he with he | he
      · rcases he with he | he
        · exact v2a he he'
        · exact v2b he he'
      · exact v2c he he'
  have hT₃ : Disjoint (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) (walkEdges T₃) :=
    Set.disjoint_left.mpr fun e he he' => by
      rcases he with he | he
      · rcases he with he | he
        · exact v3a he he'
        · exact v3b he he'
      · exact v3c he he'
  have hT₄ : Disjoint (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) (walkEdges T₄) :=
    Set.disjoint_left.mpr fun e he he' => by
      rcases he with he | he
      · rcases he with he | he
        · exact v4a he he'
        · exact v4b he he'
      · exact v4c he he'
  have hT₅ : Disjoint (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) (walkEdges T₅) :=
    Set.disjoint_left.mpr fun e he he' => by
      rcases he with he | he
      · rcases he with he | he
        · exact v5a he he'
        · exact v5b he he'
      · exact v5c he he'
  have hW : walkEdges (W₁.append W₃) = walkEdges W₁ ∪ walkEdges W₃ := walkEdges_append W₁ W₃
  have hW2 : walkEdges (W₂.append W₃) = walkEdges W₂ ∪ walkEdges W₃ := walkEdges_append W₂ W₃
  have hsub : (walkEdges (W₁.append W₃) ∪ walkEdges (W₂.append W₃)) ⊆
      (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) := by
    intro e he
    rw [hW, hW2] at he
    simp only [Set.mem_union] at he ⊢
    tauto
  have hd : ∀ {a b : V} (T : (openGraph ω).Walk a b),
      Disjoint (walkEdges W₁ ∪ walkEdges W₂ ∪ walkEdges W₃) (walkEdges T) →
      Disjoint (walkEdges (W₁.append W₃) ∪ walkEdges (W₂.append W₃)) (walkEdges T) :=
    fun T hT => Set.disjoint_of_subset_left hsub hT
  exact ⟨walkEdges (W₁.append W₃) ∪ walkEdges (W₂.append W₃), walkEdges T₀, walkEdges T₁,
    walkEdges T₂, walkEdges T₃, walkEdges T₄, walkEdges T₅,
    (walkEdges_finite (W₁.append W₃)).union (walkEdges_finite (W₂.append W₃)),
    walkEdges_finite T₀, walkEdges_finite T₁, walkEdges_finite T₂,
    walkEdges_finite T₃, walkEdges_finite T₄, walkEdges_finite T₅,
    union_subset (walkEdges_subset (W₁.append W₃)) (walkEdges_subset (W₂.append W₃)),
    walkEdges_subset T₀, walkEdges_subset T₁, walkEdges_subset T₂,
    walkEdges_subset T₃, walkEdges_subset T₄, walkEdges_subset T₅,
    ⟨conn_mono subset_union_left (mem_conn_walkEdges (W₁.append W₃)),
      conn_mono subset_union_right (mem_conn_walkEdges (W₂.append W₃))⟩,
    mem_conn_walkEdges T₀, mem_conn_walkEdges T₁, mem_conn_walkEdges T₂,
    mem_conn_walkEdges T₃, mem_conn_walkEdges T₄, mem_conn_walkEdges T₅,
    hd T₀ hT₀, hd T₁ hT₁, hd T₂ hT₂, hd T₃ hT₃, hd T₄ hT₄, hd T₅ hT₅,
    disjoint_walkEdges T₀ T₁ s01, disjoint_walkEdges T₀ T₂ s02,
    disjoint_walkEdges T₀ T₃ s03, disjoint_walkEdges T₀ T₄ s04,
    disjoint_walkEdges T₀ T₅ s05, disjoint_walkEdges T₁ T₂ s12,
    disjoint_walkEdges T₁ T₃ s13, disjoint_walkEdges T₁ T₄ s14,
    disjoint_walkEdges T₁ T₅ s15, disjoint_walkEdges T₂ T₃ s23,
    disjoint_walkEdges T₂ T₄ s24, disjoint_walkEdges T₂ T₅ s25,
    disjoint_walkEdges T₃ T₄ s34, disjoint_walkEdges T₃ T₅ s35,
    disjoint_walkEdges T₄ T₅ s45⟩

end PercLib.CriticalLRP.TreeExpansion.SixPoint
