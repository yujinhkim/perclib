/-
Coordinator-added canonical power-law specialization of the accepted `smwx5p94b/m1`
proof. Production integration revision: `9c345df8dcb6d4027a2e61d7a7785abf4df111cf`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Refined.Compose
public import PercLib.CriticalLRP.PowerLawTreeMoments

/-!
# The refined `q = 2` moment gap at the canonical power-law law

This is only the translation-invariance wrapper of the abstract source-normalized bound;
it introduces no finite-moment or subcriticality assumption.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

/-- The canonical power-law law on `ℤ^d` has the refined `q = 2` upper diagram bound
with total factor count `2p+5`, for every positive `p`. -/
theorem latticeLongRange_moment_gap_two_le_refined (d : ℕ) (α : ℝ) (β : NNReal)
    (x y : Fin d → ℤ) {p : ℕ} (hp : 1 ≤ p) :
    I417A.momentProd (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 2 -
      I417A.rawDiff (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 2 ≤
      2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1),
        (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 3 - ℓ) *
            I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 2) x y)) +
      2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1),
        (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 4 - ℓ) *
            I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 1) x y)) := by
  apply I417FreshTwo.Refined.moment_gap_two_le_refined_transitive _
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
