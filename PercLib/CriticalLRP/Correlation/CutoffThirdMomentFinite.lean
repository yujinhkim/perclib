module

public import PercLib.CriticalLRP.Correlation.CutoffThirdMoment

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.TreeExpansion.Native

/-- The tree-graph third-moment bound of Definition I.1.5 turns a finite first
cluster-volume moment into a finite third moment at the loop-safe cutoff.
This is only the p = 3 case, not finiteness of all higher moments. -/
theorem cutoff_thirdMoment_ne_top_of_firstMoment {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 0 < r) (β : NNReal)
    (hfirst : (∫⁻ ω, Percolation.cardFun (cluster ω 0)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (fun e => CutoffKernel.cutoffSymKernel_nonneg hK hr e) β)) ≠ ∞) :
    (∫⁻ ω, (Percolation.cardFun (cluster ω 0)) ^ 3
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (fun e => CutoffKernel.cutoffSymKernel_nonneg hK hr e) β)) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (third_moment_cutoff hK r β)
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hfirst)

#print axioms PercLib.CriticalLRP.TreeExpansion.Native.cutoff_thirdMoment_ne_top_of_firstMoment

end PercLib.CriticalLRP.TreeExpansion.Native
