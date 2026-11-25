/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Canonical power-law instantiations of the ordinary and mixed tree-moment
bounds. Full profile invariance supplies the two-point form used by those
bounds, while `lrKernel_unitInterval_translation_of_pair` records the
stronger translation hypothesis needed for second-moment invariance.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Mixed
public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Final
public import PercLib.CriticalLRP.Correlation.FourthMoment.Cases
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Assembly
public import PercLib.Percolation.Bond.Ergodic
public import PercLib.Percolation.Bond.Transport
public import PercLib.CriticalLRP.VolumeMoments.SecondMoment

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

/-- The canonical power-law opening probabilities are invariant under simultaneous
right translation of both endpoints. -/
theorem lrKernel_unitInterval_translation_of_pair (d : ℕ) (α : ℝ) (β : NNReal)
    (x y g : Fin d → ℤ) :
    bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β s(x + g, y + g) =
      bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β s(x, y) := by
  have hshift := bernoulliEdgeProb_shift (lrKernel_shift_invariant d α)
    (lrKernel_nonneg d α) β g s(x, y)
  simpa only [Sym2.map_mk, add_comm] using hshift

/-- Right translation preserves the canonical power-law two-point function. -/
theorem lrKernel_tau_add_right (d : ℕ) (α : ℝ) (β : NNReal)
    (a x y : Fin d → ℤ) :
    tau (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) (x + a) (y + a) =
      tau (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y := by
  let π := bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β
  have hq : ∀ u v g : Fin d → ℤ, π s(u + g, v + g) = π s(u, v) :=
    fun u v g => lrKernel_unitInterval_translation_of_pair d α β u v g
  exact PercLib.Percolation.Bond.tau_apply_eq_of_map_law_eq (p := π)
    (Equiv.addRight a)
    (PercLib.Percolation.Bond.measurePreserving_image_sym2Map_add π hq a).map_eq x y

/-- The canonical power-law two-point function has the translation-invariant form used by the
native tree-moment theorems. -/
theorem lrKernel_tau_eq_zero_sub (d : ℕ) (α : ℝ) (β : NNReal)
    (a b : Fin d → ℤ) :
    tau (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) a b =
      tau (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) 0 (b - a) := by
  have h := lrKernel_tau_add_right d α β (-a) a b
  simpa only [add_neg_cancel, sub_eq_add_neg] using h.symm

/-- The mixed cubic tree-moment bound for the canonical power-law law. -/
theorem latticeLongRange_third_moment_mixed_le (d : ℕ) (α : ℝ) (β : NNReal) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 3 ∂(latticeLongRangeMeasure d α β) ≤
      3 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ)) ∂(latticeLongRangeMeasure d α β)) ^ 2 *
        (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 2
          ∂(latticeLongRangeMeasure d α β)) := by
  have h := third_moment_mixed_le
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (lrKernel_tau_eq_zero_sub d α β)
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

/-- The ordinary third tree-moment bound for the canonical power-law law. -/
theorem latticeLongRange_third_moment_le (d : ℕ) (α : ℝ) (β : NNReal) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 3 ∂(latticeLongRangeMeasure d α β) ≤
      3 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ)) ∂(latticeLongRangeMeasure d α β)) ^ 5 := by
  have h := Native.third_moment_native
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (lrKernel_tau_eq_zero_sub d α β)
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

/-- The ordinary fourth tree-moment bound for the canonical power-law law. -/
theorem latticeLongRange_fourth_moment_le (d : ℕ) (α : ℝ) (β : NNReal) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 4 ∂(latticeLongRangeMeasure d α β) ≤
      15 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ)) ∂(latticeLongRangeMeasure d α β)) ^ 7 := by
  have h := FivePoint.fourth_moment_le
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (lrKernel_tau_eq_zero_sub d α β)
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

/-- The mixed fourth tree-moment bound for the canonical power-law law. -/
theorem latticeLongRange_fourth_moment_mixed_le (d : ℕ) (α : ℝ) (β : NNReal) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 4 ∂(latticeLongRangeMeasure d α β) ≤
      15 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 2
        ∂(latticeLongRangeMeasure d α β)) *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ)) ∂(latticeLongRangeMeasure d α β)) ^ 4 := by
  have h := FivePoint.fourth_moment_mixed_le
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (lrKernel_tau_eq_zero_sub d α β)
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

/-- The `p = 4, k = 2` mixed tree-moment bound for the canonical power-law law. -/
theorem latticeLongRange_fourth_moment_mixed_k2_le (d : ℕ) (α : ℝ) (β : NNReal) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 4 ∂(latticeLongRangeMeasure d α β) ≤
      15 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 2
        ∂(latticeLongRangeMeasure d α β)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ)) ∂(latticeLongRangeMeasure d α β)) := by
  have h := FivePoint.fourth_moment_mixed_k2_le
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (fun x y g => lrKernel_unitInterval_translation_of_pair d α β x y g)
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

/-- The `p = 5, k = 1` mixed tree-moment bound for the canonical power-law law. -/
theorem latticeLongRange_fifth_moment_mixed_le (d : ℕ) (α : ℝ) (β : NNReal) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 5 ∂(latticeLongRangeMeasure d α β) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 2
        ∂(latticeLongRangeMeasure d α β)) *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ)) ∂(latticeLongRangeMeasure d α β)) ^ 6 := by
  have h := SixPoint.fifth_moment_le
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (fun x y g => lrKernel_unitInterval_translation_of_pair d α β x y g)
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

/-- Every admissible `k` at `p = 3` for the canonical power-law law. -/
theorem latticeLongRange_third_moment_all_k_le (d : ℕ) (α : ℝ) (β : NNReal)
    (k : ℕ) (hk : k ≤ 1) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 3 ∂(latticeLongRangeMeasure d α β) ≤
      3 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 2
        ∂(latticeLongRangeMeasure d α β)) ^ k *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))
          ∂(latticeLongRangeMeasure d α β)) ^ (5 - 3 * k) := by
  have h := FivePoint.third_moment_all_k_le
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (lrKernel_tau_eq_zero_sub d α β) k hk
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

/-- Every admissible `k` at `p = 4` for the canonical power-law law. -/
theorem latticeLongRange_fourth_moment_all_k_le (d : ℕ) (α : ℝ) (β : NNReal)
    (k : ℕ) (hk : k ≤ 2) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 4 ∂(latticeLongRangeMeasure d α β) ≤
      15 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 2
        ∂(latticeLongRangeMeasure d α β)) ^ k *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))
          ∂(latticeLongRangeMeasure d α β)) ^ (7 - 3 * k) := by
  have h := FivePoint.fourth_moment_all_k_le
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (fun x y g => lrKernel_unitInterval_translation_of_pair d α β x y g) k hk
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

/-- Finite susceptibility forces a finite third cluster moment for the canonical law. -/
theorem latticeLongRange_third_moment_ne_top_of_firstMoment (d : ℕ) (α : ℝ) (β : NNReal)
    (hfirst : (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ)) ∂(latticeLongRangeMeasure d α β)) ≠ ⊤) :
    (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 3
      ∂(latticeLongRangeMeasure d α β)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (latticeLongRange_third_moment_le d α β)
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hfirst)

/-- Finite susceptibility forces a finite fourth cluster moment for the canonical law. -/
theorem latticeLongRange_fourth_moment_ne_top_of_firstMoment (d : ℕ) (α : ℝ) (β : NNReal)
    (hfirst : (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ)) ∂(latticeLongRangeMeasure d α β)) ≠ ⊤) :
    (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 4
      ∂(latticeLongRangeMeasure d α β)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (latticeLongRange_fourth_moment_le d α β)
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hfirst)

/-- Finite susceptibility also forces a finite fourth moment through the mixed bound. -/
theorem latticeLongRange_fourth_moment_mixed_ne_top_of_firstMoment (d : ℕ) (α : ℝ)
    (β : NNReal)
    (hfirst : (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ)) ∂(latticeLongRangeMeasure d α β)) ≠ ⊤) :
    (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 4
      ∂(latticeLongRangeMeasure d α β)) ≠ ⊤ := by
  have hsecond := latticeLongRange_lintegral_clusterVol_pow_two_ne_top α β
    (0 : Fin d → ℤ) (by simpa only [Percolation.cardFun_eq_encard] using hfirst)
  refine ne_top_of_le_ne_top ?_ (latticeLongRange_fourth_moment_mixed_le d α β)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
    (by simpa only [Percolation.cardFun_eq_encard] using hsecond))
    (ENNReal.pow_ne_top hfirst)

#print axioms PercLib.CriticalLRP.TreeExpansion.lrKernel_unitInterval_translation_of_pair
#print axioms PercLib.CriticalLRP.TreeExpansion.lrKernel_tau_eq_zero_sub
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_third_moment_mixed_le
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_third_moment_le
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_fourth_moment_le
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_fourth_moment_mixed_le
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_fourth_moment_mixed_k2_le
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_fifth_moment_mixed_le
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_third_moment_all_k_le
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_fourth_moment_all_k_le
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_third_moment_ne_top_of_firstMoment
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_fourth_moment_ne_top_of_firstMoment
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_fourth_moment_mixed_ne_top_of_firstMoment

end PercLib.CriticalLRP.TreeExpansion
