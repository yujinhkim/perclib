/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Analytic assembly for 105 six-terminal diagrams. The deterministic covering and
BK parts remain explicit hypotheses of the final consumer in this module.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.FullMoment
public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.RootIndependence

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- Swap a finite `Fin 105` count through five extended terminal sums. -/
theorem tsum_fin_five_swap (F : V → V → V → V → V → Fin 105 → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' k : Fin 105, F a b c d e k) =
      ∑' k : Fin 105, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e k := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' e, ∑' k : Fin 105, F a b c d e k)
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' k : Fin 105, ∑' e, F a b c d e k :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' k : Fin 105, ∑' d, ∑' e, F a b c d e k :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' k : Fin 105, ∑' c, ∑' d, ∑' e, F a b c d e k :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' k : Fin 105, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e k :=
        tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' k : Fin 105, ∑' a, ∑' b, ∑' c, ∑' d, ∑' e, F a b c d e k :=
        ENNReal.tsum_comm

/-- A constant has exactly 105 copies over `Fin 105`. -/
theorem tsum_fin105_const (c : ℝ≥0∞) : (∑' _ : Fin 105, c) = 105 * c := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- **Conditional analytic consumer for `p = 5`, `k = 1`.** A precise pointwise
five-point event bound and exact evaluation of all 105 slot diagrams imply the native fifth
moment bound. The two supplied hypotheses keep the deterministic event and BK work visibly
separate; this declaration is not by itself the source theorem. -/
theorem fifth_moment_le_of_105diagrams [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (D : Fin 105 → V → V → V → V → V → ℝ≥0∞)
    (hpoint : ∀ y z w q r : V,
      law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤ ∑' k, D k y z w q r)
    (hsum : ∀ k : Fin 105,
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D k y z w q r) =
        FivePoint.secondMoment π 0 * (FivePoint.firstMoment π 0) ^ 6) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω 0)) ^ 5
        ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0)) ^ 2 ∂(law π)) *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0) ∂(law π)) ^ 6 := by
  have hmain :
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
        105 * (FivePoint.secondMoment π 0) * (FivePoint.firstMoment π 0) ^ 6 := by
    rw [lintegral_cardFun_five_eq π 0]
    calc
      ∑' y, ∑' z, ∑' w, ∑' q, ∑' r,
        law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' k : Fin 105, D k y z w q r :=
        ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
          ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
            ENNReal.tsum_le_tsum fun r => hpoint y z w q r
      _ = ∑' k : Fin 105, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, D k y z w q r :=
        tsum_fin_five_swap (F := fun y z w q r k => D k y z w q r)
      _ = ∑' k : Fin 105, FivePoint.secondMoment π 0 * (FivePoint.firstMoment π 0) ^ 6 :=
        tsum_congr hsum
      _ = _ := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_cast
        ring_nf
  simpa only [FivePoint.secondMoment, FivePoint.firstMoment] using hmain

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.tsum_fin_five_swap
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.tsum_fin105_const
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_le_of_105diagrams

end PercLib.CriticalLRP.TreeExpansion.SixPoint
