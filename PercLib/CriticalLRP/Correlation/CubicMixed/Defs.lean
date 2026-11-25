/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Native star-pair event for the mixed cubic tree-graph bound. Supplied by
Ultramath `smwpkxbr7` member m2.
-/
module

public import PercLib.CriticalLRP.Correlation.ThirdMoment.ArmDecomposition

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

variable {V : Type*}

/-- **The star-pair event.**  `root` and `x` admit a joint open certificate to `w`, while
`w <-> y` and `w <-> z` have open certificates disjoint from it and from each other.

The first certificate is deliberately *not* split into two: this is the object that survives as a
second-moment term after summing over `x` and `w`. -/
def StarPairEvent (root x y z w : V) : Set (Config V) :=
  {ω | ∃ U W₁ W₂ : Set (Sym2 V), U.Finite ∧ W₁.Finite ∧ W₂.Finite ∧
        U ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧
        U ∈ (conn root w ∩ conn x w) ∧ W₁ ∈ conn w y ∧ W₂ ∈ conn w z ∧
        Disjoint U W₁ ∧ Disjoint U W₂ ∧ Disjoint W₁ W₂}


end PercLib.CriticalLRP.TreeExpansion
