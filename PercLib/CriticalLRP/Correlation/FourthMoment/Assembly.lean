/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Five-point tree-graph infrastructure supplied by Ultramath `smwpj8umm` member m2
and integrated from a verified candidate. The full deterministic five-point
realization and fourth-moment theorem are not asserted by these modules.
-/
module

/-
The five-point (four-plus-one-point) deterministic input and its cover of the four-point
connection event.

`Harm5` is the precise remaining combinatorial obligation at `k = 4`: five vertices in one
component of a simple graph realise one of the fifteen rooted binary trees on the four
labelled leaves — twelve combs (an ordered pair of leaves at the two shallow branch
vertices) and three balanced trees (a split of the four leaves into two pairs).

`five_point_cover` records that this hypothesis indeed covers the event
`root ↔ x₁ ∧ root ↔ x₂ ∧ root ↔ x₃ ∧ root ↔ x₄`, so that the per-shape measure bounds of
`Shapes.lean` (seven-fold BK + union bound over the branch vertices) apply termwise.
-/
public import PercLib.CriticalLRP.Correlation.FourthMoment.Shapes

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **Per-labelling cover.**  If at every connected configuration one of the two shapes with
the fixed leaf order `(x₁, x₂, x₃, x₄)` is certified, then the fourfold connection event is
contained in the union of the comb and balanced shape events. -/
theorem pair_cover [Countable V] {root x₁ x₂ x₃ x₄ : V}
    (harm : ∀ (ω : Config V), PercLib.CriticalLRP.Connects ω root x₁ →
      PercLib.CriticalLRP.Connects ω root x₂ → PercLib.CriticalLRP.Connects ω root x₃ →
      PercLib.CriticalLRP.Connects ω root x₄ →
      CombWitness (PercLib.CriticalLRP.openGraph ω) root x₁ x₂ x₃ x₄ ∨
      BalWitness (PercLib.CriticalLRP.openGraph ω) root x₁ x₂ x₃ x₄) :
    (conn root x₁ ∩ conn root x₂ ∩ conn root x₃ ∩ conn root x₄) ⊆
      (⋃ u₁, ⋃ u₂, ⋃ u₃, CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃) ∪
      (⋃ u, ⋃ v, ⋃ w, BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w) := by
  rintro ω ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
  rcases harm ω h₁ h₂ h₃ h₄ with h | h
  · exact Or.inl (combEvent_mem h)
  · exact Or.inr (balEvent_mem h)

/-- **Closed consumer theorem for one labelling.**  Under the deterministic hypothesis that
one of the two shapes with the fixed leaf order is realised in every connected configuration,
the fourfold connection probability of the five points is bounded by the sum of the seven-factor
tree sums of the two shapes (comb and balanced), i.e. by the sum of the products of the two-point
function along the seven edges of each tree, summed over the three internal vertices. -/
theorem five_point_le_of_pair [Countable V] [Nonempty V]
    (π : Sym2 V → unitInterval) (root x₁ x₂ x₃ x₄ : V)
    (harm : ∀ (ω : Config V), PercLib.CriticalLRP.Connects ω root x₁ →
      PercLib.CriticalLRP.Connects ω root x₂ → PercLib.CriticalLRP.Connects ω root x₃ →
      PercLib.CriticalLRP.Connects ω root x₄ →
      CombWitness (PercLib.CriticalLRP.openGraph ω) root x₁ x₂ x₃ x₄ ∨
      BalWitness (PercLib.CriticalLRP.openGraph ω) root x₁ x₂ x₃ x₄) :
    law π (conn root x₁ ∩ conn root x₂ ∩ conn root x₃ ∩ conn root x₄)
      ≤ (∑' u₁, ∑' u₂, ∑' u₃,
            tau π root u₁ * tau π x₁ u₁ * tau π u₁ u₂ * tau π x₂ u₂ * tau π u₂ u₃ *
              tau π x₃ u₃ * tau π x₄ u₃)
        + (∑' u, ∑' v, ∑' w,
            tau π root u * tau π u v * tau π x₁ v * tau π x₂ v * tau π u w *
              tau π x₃ w * tau π x₄ w) := by
  have hcover := pair_cover harm
  calc law π (conn root x₁ ∩ conn root x₂ ∩ conn root x₃ ∩ conn root x₄)
      ≤ law π ((⋃ u₁, ⋃ u₂, ⋃ u₃, CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃) ∪
          (⋃ u, ⋃ v, ⋃ w, BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w)) :=
        measure_mono hcover
    _ ≤ law π (⋃ u₁, ⋃ u₂, ⋃ u₃, CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃)
          + law π (⋃ u, ⋃ v, ⋃ w, BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w) :=
        measure_union_le _ _
    _ ≤ _ := add_le_add (combEvent_le π root x₁ x₂ x₃ x₄) (balEvent_le π root x₁ x₂ x₃ x₄)





/-- The conditional full fifteen-shape five-point bound, in the same labelling and order as
`Harm5` and `fivePointDiagram`. The deterministic realization remains an input. -/
theorem five_point_le_of_harm [Countable V] (π : Sym2 V → unitInterval)
    (root x₁ x₂ x₃ x₄ : V)
    (harm : ∀ (ω : Config V), PercLib.CriticalLRP.Connects ω root x₁ →
      PercLib.CriticalLRP.Connects ω root x₂ → PercLib.CriticalLRP.Connects ω root x₃ →
      PercLib.CriticalLRP.Connects ω root x₄ →
      Harm5 (PercLib.CriticalLRP.openGraph ω) root x₁ x₂ x₃ x₄) :
    law π (conn root x₁ ∩ conn root x₂ ∩ conn root x₃ ∩ conn root x₄) ≤
      fivePointDiagram π root x₁ x₂ x₃ x₄ := by
  have hbound : ∀ k : Fin 15,
      law π (fivePointShapeEvent k root x₁ x₂ x₃ x₄) ≤
        fivePointIndexedDiagram π k root x₁ x₂ x₃ x₄ := by
    intro k
    fin_cases k <;> dsimp [fivePointShapeEvent, fivePointIndexedDiagram]
    exacts
[    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₁ x₂ x₃ x₄),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₁ x₃ x₂ x₄),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₁ x₄ x₂ x₃),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₂ x₁ x₃ x₄),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₂ x₃ x₁ x₄),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₂ x₄ x₁ x₃),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₃ x₁ x₂ x₄),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₃ x₂ x₁ x₄),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₃ x₄ x₁ x₂),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₄ x₁ x₂ x₃),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₄ x₂ x₁ x₃),
    (by simpa only [combShapeEvent, combDiagram] using combEvent_le π root x₄ x₃ x₁ x₂),
    (by simpa only [balShapeEvent, balDiagram] using balEvent_le π root x₁ x₂ x₃ x₄),
    (by simpa only [balShapeEvent, balDiagram] using balEvent_le π root x₁ x₃ x₂ x₄),
    (by simpa only [balShapeEvent, balDiagram] using balEvent_le π root x₁ x₄ x₂ x₃)]
  have hcover : (conn root x₁ ∩ conn root x₂ ∩ conn root x₃ ∩ conn root x₄) ⊆
      ⋃ k : Fin 15, fivePointShapeEvent k root x₁ x₂ x₃ x₄ := by
    rintro ω ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
    have h := harm ω h₁ h₂ h₃ h₄
    simp only [Harm5] at h
    simp only [Set.mem_iUnion]
    rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
    · exact ⟨0, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h1⟩
    · exact ⟨1, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h2⟩
    · exact ⟨2, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h3⟩
    · exact ⟨3, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h4⟩
    · exact ⟨4, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h5⟩
    · exact ⟨5, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h6⟩
    · exact ⟨6, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h7⟩
    · exact ⟨7, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h8⟩
    · exact ⟨8, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h9⟩
    · exact ⟨9, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h10⟩
    · exact ⟨10, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h11⟩
    · exact ⟨11, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using combEvent_mem h12⟩
    · exact ⟨12, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using balEvent_mem h13⟩
    · exact ⟨13, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using balEvent_mem h14⟩
    · exact ⟨14, by simpa [fivePointShapeEvent, combShapeEvent, balShapeEvent, Set.mem_iUnion] using balEvent_mem h15⟩
  calc
    law π (conn root x₁ ∩ conn root x₂ ∩ conn root x₃ ∩ conn root x₄)
        ≤ law π (⋃ k : Fin 15, fivePointShapeEvent k root x₁ x₂ x₃ x₄) := measure_mono hcover
    _ ≤ ∑' k : Fin 15, law π (fivePointShapeEvent k root x₁ x₂ x₃ x₄) := measure_iUnion_le _
    _ ≤ ∑' k : Fin 15, fivePointIndexedDiagram π k root x₁ x₂ x₃ x₄ :=
      ENNReal.tsum_le_tsum hbound
    _ = ∑ k : Fin 15, fivePointIndexedDiagram π k root x₁ x₂ x₃ x₄ := tsum_fintype _
    _ = fivePointDiagram π root x₁ x₂ x₃ x₄ := by
      norm_num [Fin.sum_univ_succ, fivePointIndexedDiagram, fivePointDiagram]
      ring

end PercLib.CriticalLRP.TreeExpansion.FivePoint
