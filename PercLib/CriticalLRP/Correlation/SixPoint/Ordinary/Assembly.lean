/-
Closing composition: m1's (direction A + C) interface applied to m2's (direction B) diagram
evaluation.  This file contains no new mathematics; it checks that `Main.ordD_eval` is exactly
the remaining input of `Nine.NineFull`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.Main
public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.NineFull

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- **Target theorem.**  The ordinary (`k = 0`) `p = 5` fifth cluster-moment inequality,
unconditional in profile invariance `hq` on a countable additive group. -/
theorem fifth_moment_ordinary_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 :=
  fifth_moment_ordinary_le_of_ordDEval_eq π fun k j => ordD_eval π hq k j

/-- **Canonical form.**  The ordinary `p = 5` fifth-moment inequality at the paper's law
`latticeLongRangeMeasure d α β` (kernel `‖x-y‖^{-d-α}`).  No finite-moment, subcriticality or
critical-sharpness hypothesis occurs, and no conditional input remains. -/
theorem latticeLongRange_fifth_moment_ordinary_le_uncond (d : ℕ) (α : ℝ) (β : NNReal) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 5
        ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))
        ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ^ 9 := by
  have h := fifth_moment_ordinary_le
    (PercLib.CriticalLRP.bernoulliEdgeProb (PercLib.CriticalLRP.lrKernel d α)
      (PercLib.CriticalLRP.lrKernel_nonneg d α) β)
    (fun x y g => PercLib.CriticalLRP.TreeExpansion.lrKernel_unitInterval_translation_of_pair
      d α β x y g)
  simpa only [PercLib.CriticalLRP.latticeLongRangeMeasure, PercLib.CriticalLRP.longRangeMeasure]
    using h

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.latticeLongRange_fifth_moment_ordinary_le_uncond

end PercLib.CriticalLRP.TreeExpansion.SixPoint
