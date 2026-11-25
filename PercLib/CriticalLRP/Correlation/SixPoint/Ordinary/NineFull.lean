/-
The complete interface: direction A's event bound, the bridge to direction B's diagram
(`ordD`), and direction C's compiled consumer.

Once direction B evaluates its diagram,

  `∀ k j, (∑' y z w q r, ordD π k j ![0, y, z, w, q, r]) ≤ (∑' x, tau π 0 x) ^ 9`,

the ordinary fifth-moment inequality follows immediately; nothing else is assumed.

Supplied by Ultramath `smwpv4yqm` member `m1` (direction d3, task direction A).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.NineBridge
public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.NineIntegration

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- **Final interface.**  Direction B's evaluation of its own diagram `ordD`, together with the
compiled event side and consumer, gives the ordinary fifth-moment inequality
`∫⁻ |K₀|^5 ≤ 105 * (∫⁻ |K₀|)^9`. -/
theorem fifth_moment_ordinary_le_of_ordDEval [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ordD π k j ![0, y, z, w, q, r]) ≤
        (∑' x, tau π 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 :=
  fifth_moment_ordinary_le_of_nineShapeEval π fun k j =>
    (tsum_congr fun _ => tsum_congr fun _ => tsum_congr fun _ => tsum_congr fun _ =>
      tsum_congr fun _ => nineShapeChunk_eq_ordD π _ k j).trans_le (hE k j)

/-- The equality form of direction B's evaluation. -/
theorem fifth_moment_ordinary_le_of_ordDEval_eq [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ordD π k j ![0, y, z, w, q, r]) =
        (∑' x, tau π 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 :=
  fifth_moment_ordinary_le_of_ordDEval π fun k j => (hE k j).le

/-! ## Canonical instantiation at `latticeLongRangeMeasure d α β` -/

/-- **Canonical form.**  At `latticeLongRangeMeasure d α β`, direction A's event bound and
direction C's consumer reduce the ordinary fifth-moment inequality to direction B's evaluation
of the nine-tau diagram.  No finite-moment, subcriticality or critical-sharpness hypothesis is
used; the profile is the translation-invariant `bernoulliEdgeProb (lrKernel d α)`. -/
theorem latticeLongRange_fifth_moment_ordinary_le_of_nineShapeEval (d : ℕ) (α : ℝ)
    (β : NNReal)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y : Fin d → ℤ, ∑' z : Fin d → ℤ, ∑' w : Fin d → ℤ, ∑' q : Fin d → ℤ,
          ∑' r : Fin d → ℤ,
        nineShapeChunk
          (PercLib.CriticalLRP.bernoulliEdgeProb (PercLib.CriticalLRP.lrKernel d α)
            (PercLib.CriticalLRP.lrKernel_nonneg d α) β) ![0, y, z, w, q, r] k j) ≤
        (∑' x : Fin d → ℤ,
          tau (PercLib.CriticalLRP.bernoulliEdgeProb (PercLib.CriticalLRP.lrKernel d α)
            (PercLib.CriticalLRP.lrKernel_nonneg d α) β) 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))) ^ 5
        ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : Fin d → ℤ))
        ∂(PercLib.CriticalLRP.latticeLongRangeMeasure d α β)) ^ 9 :=
  latticeLongRange_fifth_moment_ordinary_le d α β
    (fun k j y z w q r =>
      nineShapeChunk (PercLib.CriticalLRP.bernoulliEdgeProb (PercLib.CriticalLRP.lrKernel d α)
        (PercLib.CriticalLRP.lrKernel_nonneg d α) β) ![0, y, z, w, q, r] k j)
    (fun k j y z w q r => law_sixShape_le_nineShapeChunk_root _ k j y z w q r) hE

end PercLib.CriticalLRP.TreeExpansion.SixPoint

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_ordDEval
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_ordDEval_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.latticeLongRange_fifth_moment_ordinary_le_of_nineShapeEval
