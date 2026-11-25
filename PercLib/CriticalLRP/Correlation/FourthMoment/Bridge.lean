/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Conversion from the normalized five-terminal comb construction to the
comb/balanced events used in the fourth-moment analytical assembly.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Attach
public import PercLib.CriticalLRP.Correlation.FourthMoment.FullMoment

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

private theorem pairwiseSeven {α : Type*} {l0 l1 l2 l3 l4 l5 l6 : List α}
    (h : (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6).Nodup) :
    [l0, l1, l2, l3, l4, l5, l6].Pairwise List.Disjoint := by
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, d01, d02, d03, d04, d05, d06,
    d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ :=
    nodup_append7_facts h
  simp_all [List.pairwise_cons]

/-- The first-slot ordering is exactly a comb witness with seven disjoint arms. -/
theorem combWitness_of_slots {G : SimpleGraph V} {root x₁ x₂ x₃ x₄ u v w : V}
    (h : CombSlots G root x₁ x₂ x₃ x₄ u v w) : CombWitness G root x₁ x₂ x₃ x₄ := by
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, hnd⟩ := h
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, d01, d02, d03, d04, d05, d06,
    d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ :=
    nodup_append7_facts hnd
  refine ⟨u, v, w, p0, p1, s1, p2, s2, p3, p4, ?_⟩
  apply pairwiseSeven
  exact nodup_seven n0 n1 n5 n2 n6 n3 n4 d01 d05 d02 d06 d03 d04 d15 d12 d16 d13 d14
    d25.symm d56 d35.symm d45.symm d26 d23 d24 d36.symm d46.symm d34

/-- With the singleton leaf in the middle slot, reversing the first spine segment gives the
balanced witness. The endpoint reversals do not change disjointness of edge sets. -/
theorem balWitness_of_slots {G : SimpleGraph V} {x₁ x₂ root x₃ x₄ u v w : V}
    (h : CombSlots G x₁ x₂ root x₃ x₄ u v w) : BalWitness G root x₁ x₂ x₃ x₄ := by
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, hnd⟩ := h
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, d01, d02, d03, d04, d05, d06,
    d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ :=
    nodup_append7_facts hnd
  refine ⟨v, u, w, p2, s1.reverse, p0, p1, s2, p3, p4, ?_⟩
  simp only [SimpleGraph.Walk.edges_reverse]
  apply pairwiseSeven
  exact nodup_seven n2 (List.nodup_reverse.mpr n5) n0 n1 n6 n3 n4
    (List.disjoint_reverse_right.mpr d25) d02.symm d12.symm d26 d23 d24
    (List.disjoint_reverse_left.mpr d05.symm) (List.disjoint_reverse_left.mpr d15.symm)
    (List.disjoint_reverse_left.mpr d56) (List.disjoint_reverse_left.mpr d35.symm)
    (List.disjoint_reverse_left.mpr d45.symm)
    d01 d06 d03 d04 d16 d13 d14 d36.symm d46.symm d34

#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.combWitness_of_slots
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.balWitness_of_slots



/-- Every normalized five-terminal slot realization gives one of the fifteen `Harm5` shapes. -/
theorem harm5_of_combShape {G : SimpleGraph V} (root x₁ x₂ x₃ x₄ : V)
    (h : ∃ k : Fin 15, ∃ u v w, CombShape G k u v w ![root, x₁, x₂, x₃, x₄]) :
    Harm5 G root x₁ x₂ x₃ x₄ := by
  obtain ⟨k, u, v, w, h⟩ := h
  fin_cases k <;> simp_all [CombShape, pat, Harm5]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (balWitness_of_slots h)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (balWitness_of_slots h))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (balWitness_of_slots h))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (combWitness_of_slots h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (combWitness_of_slots h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (combWitness_of_slots h))))))))))
  · exact Or.inl (combWitness_of_slots h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (combWitness_of_slots h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (combWitness_of_slots h)))))))))))
  · exact Or.inr (Or.inl (combWitness_of_slots h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (combWitness_of_slots h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (combWitness_of_slots h))))))))))))
  · exact Or.inr (Or.inr (Or.inl (combWitness_of_slots h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (combWitness_of_slots h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (combWitness_of_slots h)))))))))

/-- **The ordinary fourth cluster-moment tree bound for a translation-invariant Bernoulli
bond law.** No moment-finiteness hypothesis remains. -/
theorem fourth_moment_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0)) ^ 4 ∂(law π) ≤
      15 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω 0) ∂(law π)) ^ 7 := by
  apply fourth_moment_le_of_harm π hinv
  intro y z w q ω h1 h2 h3 h4
  exact harm5_of_combShape (G := openGraph ω) 0 y z w q (exists_combShape_connects ω 0 y z w q h1 h2 h3 h4)

#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.harm5_of_combShape
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.fourth_moment_le

end PercLib.CriticalLRP.TreeExpansion.FivePoint
