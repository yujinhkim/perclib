/-
Swarm `smwxk27m7`: coordinator assembly of the independently rebuilt `m1`, `m2`,
and the reviewed mirror core of `m3`.

The unconditional `p = 5`, `k = 2` fifth-moment bound on a countable additive
commutative group with full translation invariance of the two-point profile.
No moment-finiteness assumption and no additional event-cover hypothesis.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation3.Assemble
public import PercLib.CriticalLRP.Correlation.SixPoint.SocketMirror.Main
public import PercLib.CriticalLRP.PowerLawTreeMoments

/-!
# The `p = 5`, `k = 2` moment bound
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval3

set_option linter.style.longLine false
set_option linter.style.setOption false

variable {V : Type*}

/-- **Lemma I.4.16 at `p = 5`, `k = 2`.**  The middle split is handled by
`K2Mass.shapeTotal_mid_le`; the splits `0,1,5,6` by the reviewed socket-to-shape bridge,
split `3` by the measured event bound, and split `4` by its exact mirror to split `3`.
The coefficients remain the native `15 * 7 = 105`; no moment is assumed finite. -/
theorem fifth_moment_mixed_k2_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  exact fifth_moment_k2_le_of_rootSlot_four π hq
    (SocketMirror.shapeTotal_patSlot0_four_le_of_three π 0
      (SplitEval2.J3.shapeTotal_rootSlot0_three_le π hq))
    (SocketMirror.shapeTotal_patSlot2_four_le_of_three π 0
      (SplitEval2.J3.shapeTotal_rootSlot2_three_le π hq))

end PercLib.CriticalLRP.SixPoint.SplitEval3

namespace PercLib.CriticalLRP.TreeExpansion

/-- **The `p = 5`, `k = 2` bound at the canonical power-law law on $\bZ^d$.**
The profile-invariance premise is the proved translation invariance of `lrKernel`; no
subcriticality, sharpness or finite-moment premise is used. -/
theorem latticeLongRange_fifth_moment_mixed_k2_le (d : ℕ) (α : ℝ) (β : NNReal) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 5
      ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 2
        ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))
          ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ^ 3 := by
  have h := PercLib.CriticalLRP.SixPoint.SplitEval3.fifth_moment_mixed_k2_le
    (V := Fin d → ℤ)
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (fun x y g => lrKernel_unitInterval_translation_of_pair d α β x y g)
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

end PercLib.CriticalLRP.TreeExpansion
