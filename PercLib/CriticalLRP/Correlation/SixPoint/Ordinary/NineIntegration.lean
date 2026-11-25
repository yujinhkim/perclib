/-
Interface test: the direction-A event bound (`Nine.NineCover`) plugs into the direction-C
compiled consumer (`m3: Ordinary.Consumer`) with no statement mismatch, leaving exactly the
direction-B diagram evaluation as a hypothesis.

The diagram is `nineShapeChunk π ![0, y, z, w, q, r] k j` (nine tau factors, the four internal
vertices `c, u, v, w` summed out).  `hE` is the only remaining input.

Supplied by Ultramath `smwpv4yqm` member `m1` (direction d3, task direction A).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.NineCover
public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.Consumer

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- **A + C composed**: given the direction-B diagram evaluation for the direction-A diagram
(`nineShapeChunk`), the ordinary fifth-moment inequality follows.  The event side is supplied
by `sixPoint_le_nineShapeSum_conn`; nothing else is assumed. -/
theorem fifth_moment_ordinary_le_of_nineShapeEval [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, nineShapeChunk π ![0, y, z, w, q, r] k j) ≤
        (∑' x, tau π 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 :=
  fifth_moment_ordinary_le_of_nineChunks π
    (fun k j y z w q r => nineShapeChunk π ![0, y, z, w, q, r] k j)
    (fun y z w q r => sixPoint_le_nineShapeSum_conn π y z w q r) hE

/-- The equality form of the same composition. -/
theorem fifth_moment_ordinary_le_of_nineShapeEval_eq [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hE : ∀ (k : Fin 15) (j : Fin 7),
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, nineShapeChunk π ![0, y, z, w, q, r] k j) =
        (∑' x, tau π 0 x) ^ 9) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 9 :=
  fifth_moment_ordinary_le_of_nineChunks_eq π
    (fun k j y z w q r => nineShapeChunk π ![0, y, z, w, q, r] k j)
    (fun y z w q r => sixPoint_le_nineShapeSum_conn π y z w q r) hE

end PercLib.CriticalLRP.TreeExpansion.SixPoint

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_nineShapeEval
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.fifth_moment_ordinary_le_of_nineShapeEval_eq
