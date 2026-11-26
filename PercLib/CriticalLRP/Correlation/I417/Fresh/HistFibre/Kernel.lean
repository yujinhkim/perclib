/-
Coordinator extension of the independently reviewed `smwxfstjy/m1` history-fibre evaluation.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistFibre.Final
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Spine.Main

/-!
# The symmetric two-point kernel in the printed orientation

The fibre evaluation holds with an arbitrary two-point kernel. For the genuine percolation
kernel, its symmetry allows `T^ℓ(y,w)` to be rewritten as `T^ℓ(w,y)` without an independence or
finiteness hypothesis.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417HistFibre

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-- One branch fibre in the actual two-point kernel, with the orientation `T^ℓ(w,y)` used by
`genFreshProfile`. This is only the orientation extension of the already-evaluated fibre, not
its assembly over split choices or pinned labelled arms. -/
theorem tsum_histFibre_kernel_markDepth {n : ℕ} (π : Sym2 V → unitInterval) (χ : ℝ≥0∞)
    (hχ : ∀ a : V, ∑' b : V, I417FreshTwo.kernel π a b = χ)
    (k : (t : Fin n) → I417GenIter.Idx t) (y w : V) :
    (∑' ga : V, I417HistToSpine.histFibre (fun _ => I417FreshTwo.kernel π) y w k ga) =
      χ ^ (2 * (n + 1) - I417FreshDepth.markDepthK n k) *
        I417Base.iterPow (I417FreshTwo.kernel π) (I417FreshDepth.markDepthK n k) w y := by
  rw [tsum_histFibre_markDepth (I417FreshTwo.kernel π) χ hχ k y w,
    I417Base.iterPow_comm (I417FreshTwo.kernel π)
      (fun a b => I417FreshFour.Eval.tau_symm π a b) (I417FreshDepth.markDepthK n k) y w]

set_option linter.hashCommand false

#print axioms tsum_histFibre_kernel_markDepth

end PercLib.CriticalLRP.I417HistFibre
