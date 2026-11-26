/-
Coordinator-added canonical power-law specialization of the reviewed `smwx6p0op/m1`
proof. Production integration revision: `3cd318e5a37d0dc889f23bd3baf1b8884e651a27`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Three.Refined.Compose
public import PercLib.CriticalLRP.PowerLawTreeMoments

/-!
# The refined `q = 3` moment gap at the canonical power-law law

This is only the translation-invariance wrapper of the abstract source-normalized bound.
It introduces no finite-moment or subcriticality premise.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

/-- The canonical power-law law on `ℤ^d` has the refined `q = 3` moment-gap bound
with total factor count `2p+7`, for every positive `p`. -/
theorem latticeLongRange_moment_gap_three_le_refined (d : ℕ) (α : ℝ) (β : NNReal)
    (x y : Fin d → ℤ) {p : ℕ} (hp : 1 ≤ p) :
    I417A.momentProd (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 3 -
      I417A.rawDiff (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 3 ≤
      3 * (∑ ℓ ∈ Finset.Icc 2 (p + 1),
        (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (2 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 4 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 3) x y) +
          3 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 5 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 2) x y) +
          3 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 6 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 1) x y))) := by
  apply I417FreshThree.Refined.moment_gap_three_le_refined_transitive _
    (fun e => bernoulliEdgeProb_lt_one (lrKernel_nonneg d α) β e) x y p hp
  intro v
  let g : (Fin d → ℤ) ≃ (Fin d → ℤ) := Equiv.addRight (v - x)
  refine ⟨g, ?_, ?_⟩
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
        simpa only [Sym2.map_mk, Equiv.coe_addRight, g] using
          lrKernel_unitInterval_translation_of_pair d α β a b (v - x)
  · simp [g]

end PercLib.CriticalLRP.TreeExpansion
