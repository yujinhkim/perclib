/- Canonical power-law instantiation of the integrated I.4.17 `p = 2, q = 1` theorem. -/

module

public import PercLib.CriticalLRP.Correlation.I417Example.Main
public import PercLib.CriticalLRP.PowerLawTreeMoments

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

open PercLib.CriticalLRP.I417

/-- **Lemma I.4.17 at `p = 2`, `q = 1` for the canonical power-law law on `ℤ^d`.**
Translation invariance of `lrKernel` supplies the transitivity hypothesis; no finite-moment or
subcriticality premise is added.  `bernoulliEdgeProb (lrKernel d α) ... β` is the opening profile
of `latticeLongRangeMeasure d α β`. -/
theorem latticeLongRange_I417_p21_printed (d : ℕ) (α : ℝ) (β : NNReal)
    (x y : Fin d → ℤ) :
    volSq (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x *
        meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) y -
        exclMomentSq (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y ≤
      T3 (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y *
          (meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^ 4 +
        2 * T4 (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y *
          (meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^ 3 := by
  apply printed_le_of_transitive _ (fun e => bernoulliEdgeProb_lt_one (lrKernel_nonneg d α) β e)
  intro v
  let g : (Fin d → ℤ) ≃ (Fin d → ℤ) := Equiv.addRight (v - x)
  refine ⟨g, ?_, ?_⟩
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
        simpa only [Sym2.map_mk, Equiv.coe_addRight, g] using
          TreeExpansion.lrKernel_unitInterval_translation_of_pair d α β a b (v - x)
  · simp [g]

end PercLib.CriticalLRP.I417Example
