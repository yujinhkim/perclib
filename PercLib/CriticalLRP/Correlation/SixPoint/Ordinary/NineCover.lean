/-
The ordinary (`k = 0`) event-side bound over the `105 = 15 * 7` shapes: composing the committed
six-terminal cover (`Attachment.Assembly.sixPoint_le_sixShapeChunk`) with the per-shape
nine-singleton BK bound (`Nine.NineShape.law_sixShape_le_nineShapeDiag`).

This is *not* the fifth-moment inequality: it stops at the sum of the `105` nine-tau diagrams.
Evaluating each diagram to `chi^9` (hence producing `105 * chi^9`) is a separate step.

Supplied by Ultramath `smwpv4yqm` member `m1` (direction d3, task direction A).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Ordinary.NineShape
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Assembly

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Probability
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-- **The `105`-shape nine-tau bound.**  The six-point connection event is at most the sum, over
the `15 * 7` six-terminal shapes and the four internal vertices `c, u, v, w`, of the nine-tau
diagrams.  Every internal vertex sum is retained; there is no joint pair. -/
theorem sixPoint_le_nineShapeSum [Countable V] (π : Sym2 V → unitInterval) (T : Fin 6 → V) :
    law π (⋂ i : Fin 6,
        {ω : PercLib.CriticalLRP.Config V | PercLib.CriticalLRP.Connects ω (T 0) (T i)}) ≤
      ∑' k : Fin 15, ∑' j : Fin 7, ∑' c : V, ∑' u : V, ∑' v : V, ∑' w : V,
        nineShapeDiag π T k j c u v w := by
  refine (sixPoint_le_sixShapeChunk π T).trans ?_
  exact ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun j =>
    law_sixShape_le_nineShapeDiag π T k j

/-- The same bound for the root tuple `(0, y, z, w, q, r)`, with the six-point intersection
rewritten as an intersection of five two-point connections. -/
theorem sixPoint_le_nineShapeSum_conn [Countable V] [Zero V] (π : Sym2 V → unitInterval)
    (y z w q r : V) :
    law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
      ∑' k : Fin 15, ∑' j : Fin 7, ∑' c : V, ∑' u : V, ∑' v : V, ∑' w' : V,
        nineShapeDiag π ![0, y, z, w, q, r] k j c u v w' := by
  rw [← iInter_six_conn y z w q r]
  exact sixPoint_le_nineShapeSum π ![0, y, z, w, q, r]

end PercLib.CriticalLRP.TreeExpansion.SixPoint

#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.sixPoint_le_nineShapeSum
#print axioms PercLib.CriticalLRP.TreeExpansion.SixPoint.sixPoint_le_nineShapeSum_conn
