/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Five-point tree-graph infrastructure supplied by Ultramath `smwpj8umm` member m2
and integrated from a verified candidate. The full deterministic five-point
realization and fourth-moment theorem are not asserted by these modules.
-/
module

/-
Measure bounds for one five-point tree shape: seven-fold BK plus a union bound over the
branch vertices.  Each shape costs the product of the seven two-point factors along its
edges, summed over its three (unlabelled) internal vertices.
-/
public import PercLib.CriticalLRP.Correlation.FourthMoment.Defs

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **One comb shape.**  The comb with leaves `x₁` at `u₁`, `x₂` at `u₂` and `x₃, x₄` at
`u₃` has probability at most the seven-factor tree sum. -/
theorem combEvent_le [Countable V] (π : Sym2 V → unitInterval) (root x₁ x₂ x₃ x₄ : V) :
    law π (⋃ u₁, ⋃ u₂, ⋃ u₃, CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃)
      ≤ ∑' u₁, ∑' u₂, ∑' u₃,
          tau π root u₁ * tau π x₁ u₁ * tau π u₁ u₂ * tau π x₂ u₂ * tau π u₂ u₃ *
            tau π x₃ u₃ * tau π x₄ u₃ := by
  have hterm : ∀ u₁ u₂ u₃ : V, law π (CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃)
      ≤ tau π root u₁ * tau π x₁ u₁ * tau π u₁ u₂ * tau π x₂ u₂ * tau π u₂ u₃ *
          tau π x₃ u₃ * tau π x₄ u₃ := by
    intro u₁ u₂ u₃
    have h := prodBernoulli_seven_wit_le (p := π)
      (A₀ := conn root u₁) (A₁ := conn x₁ u₁) (A₂ := conn u₁ u₂) (A₃ := conn x₂ u₂)
      (A₄ := conn u₂ u₃) (A₅ := conn x₃ u₃) (A₆ := conn x₄ u₃)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
    refine h.trans (le_of_eq ?_)
    ac_rfl
  calc law π (⋃ u₁, ⋃ u₂, ⋃ u₃, CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃)
      ≤ ∑' u₁, law π (⋃ u₂, ⋃ u₃, CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃) :=
        measure_iUnion_le _
    _ ≤ ∑' u₁, ∑' u₂, law π (⋃ u₃, CombEvent (V := V) root x₁ x₂ x₃ x₄ u₁ u₂ u₃) :=
        ENNReal.tsum_le_tsum fun u₁ => measure_iUnion_le _
    _ ≤ ∑' u₁, ∑' u₂, ∑' u₃,
          tau π root u₁ * tau π x₁ u₁ * tau π u₁ u₂ * tau π x₂ u₂ * tau π u₂ u₃ *
            tau π x₃ u₃ * tau π x₄ u₃ :=
        ENNReal.tsum_le_tsum fun u₁ => ENNReal.tsum_le_tsum fun u₂ =>
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun u₃ => hterm u₁ u₂ u₃)

/-- **One balanced shape.**  The balanced tree with pairs `{x₁,x₂}` at `v` and `{x₃,x₄}` at
`w`, both below `u`, has probability at most its seven-factor tree sum. -/
theorem balEvent_le [Countable V] (π : Sym2 V → unitInterval) (root x₁ x₂ x₃ x₄ : V) :
    law π (⋃ u, ⋃ v, ⋃ w, BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w)
      ≤ ∑' u, ∑' v, ∑' w,
          tau π root u * tau π u v * tau π x₁ v * tau π x₂ v * tau π u w *
            tau π x₃ w * tau π x₄ w := by
  have hterm : ∀ u v w : V, law π (BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w)
      ≤ tau π root u * tau π u v * tau π x₁ v * tau π x₂ v * tau π u w *
          tau π x₃ w * tau π x₄ w := by
    intro u v w
    have h := prodBernoulli_seven_wit_le (p := π)
      (A₀ := conn root u) (A₁ := conn u v) (A₂ := conn x₁ v) (A₃ := conn x₂ v)
      (A₄ := conn u w) (A₅ := conn x₃ w) (A₆ := conn x₄ w)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
      (PercLib.CriticalLRP.isIncreasing_connects _ _)
    refine h.trans (le_of_eq ?_)
    ac_rfl
  calc law π (⋃ u, ⋃ v, ⋃ w, BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w)
      ≤ ∑' u, law π (⋃ v, ⋃ w, BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w) :=
        measure_iUnion_le _
    _ ≤ ∑' u, ∑' v, law π (⋃ w, BalEvent (V := V) root x₁ x₂ x₃ x₄ u v w) :=
        ENNReal.tsum_le_tsum fun u => measure_iUnion_le _
    _ ≤ ∑' u, ∑' v, ∑' w,
          tau π root u * tau π u v * tau π x₁ v * tau π x₂ v * tau π u w *
            tau π x₃ w * tau π x₄ w :=
        ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v =>
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun w => hterm u v w)

end PercLib.CriticalLRP.TreeExpansion.FivePoint
