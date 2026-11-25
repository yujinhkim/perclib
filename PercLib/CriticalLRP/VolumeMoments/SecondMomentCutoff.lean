/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.SecondMoment
public import PercLib.CriticalLRP.VolumeMoments.FiniteCutoffModel
public import PercLib.CriticalLRP.VolumeMoments.ErrorBounds

/-
Finiteness of the second moment at the Definition I.1.5 cutoff law follows from
finiteness of the first. The remaining input is subcritical finiteness of the
mean, not an independently assumed second-moment bound.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.Hvol

open MeasureTheory
open scoped ENNReal NNReal

/-- The `cardFun`-product second moment in the I.4.7 cutoff theorem is finite as
soon as the first moment of the same cutoff law is finite. -/

theorem cutoffSecondMoment_ne_top_of_firstMoment (K : ℝ → ℝ)
    (hK : AntitoneOn K (Set.Ioi 0)) (d : ℕ) (r : ℝ) (hr : 0 < r)
    (β : NNReal) (x : Fin d → ℤ)
    (h1 : (∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞) :
    (∫⁻ ω, Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞ := by
  have h1' : (∫⁻ ω, clusterVol ω x
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞ := by
    simpa only [Percolation.cardFun_eq_encard] using h1
  have hS : ∀ a : Fin d → ℤ,
      (∫⁻ ω, clusterVol ω a
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≤
      ∫⁻ ω, clusterVol ω x
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) := by
    intro a
    have hs := lintegral_clusterVol_shift_invariant
      (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
      (bernoulliEdgeProb_shift (CutoffKernel.cutoffSymKernel_shift K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    simp only [longRangeMeasure]
    rw [hs a, hs x]
  have hs := lintegral_clusterVol_sq_ne_top
    (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
      (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)
    (fun e => bernoulliEdgeProb_lt_one (CutoffKernel.cutoffSymKernel_nonneg hK hr) β e)
    x hS (by simpa only [longRangeMeasure] using h1')
  simpa only [longRangeMeasure, pow_two, Percolation.cardFun_eq_encard] using hs


/-- The joint window moment used by I.4.7 and I.4.11 is finite under the same
finite-first-moment premise. -/

theorem cutoffJointSecondMoment_ne_top_of_firstMoment (K : ℝ → ℝ)
    (hK : AntitoneOn K (Set.Ioi 0)) (d : ℕ) (r : ℝ) (hr : 0 < r)
    (β : NNReal) (x : Fin d → ℤ) (B : Finset (Fin d → ℤ))
    (h1 : (∫⁻ ω, Percolation.cardFun (cluster ω x)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞) :
    (∫⁻ ω, Percolation.cardFun (cluster ω x) *
        ∑ y ∈ B, Percolation.cardFun (cluster ω y)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞ := by
  have hi := bernoulliEdgeProb_shift (CutoffKernel.cutoffSymKernel_shift K d r)
    (CutoffKernel.cutoffSymKernel_nonneg hK hr) β
  have hsecond : ∀ a : Fin d → ℤ,
      (∫⁻ ω, Percolation.cardFun (cluster ω a) * Percolation.cardFun (cluster ω a)
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) ≠ ∞ := by
    intro a
    refine cutoffSecondMoment_ne_top_of_firstMoment K hK d r hr β a ?_
    rw [show (∫⁻ ω, Percolation.cardFun (cluster ω a)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (CutoffKernel.cutoffSymKernel_nonneg hK hr) β)) =
      ∫⁻ ω, Percolation.cardFun (cluster ω x)
        ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
          (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) by
      simpa only [longRangeMeasure] using Hvol.hvol_cardFun hi x a]
    exact h1
  have hs := joint_windowMoment_le_sum_second_moments
    (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
      (CutoffKernel.cutoffSymKernel_nonneg hK hr) β) x B
  refine ne_top_of_le_ne_top ?_ (by simpa only [longRangeMeasure] using hs)
  rw [ENNReal.sum_ne_top]
  intro y _
  exact ENNReal.add_ne_top.mpr ⟨hsecond x, hsecond y⟩

end PercLib.CriticalLRP.Hvol
