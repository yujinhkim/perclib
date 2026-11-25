/-
# Exact support of the cutoff derivative weight

Accepted from swarm `smwtvrwnn` member `m3`, direction d10.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux.Defs

/-!
The genuine (non-loop, in-range) support of the cutoff derivative weight.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

/-- `e` is a genuine edge of length at most `r`: non-loop and inside the interaction range.
This is the exact support of the source derivative weight `M.cutEdgeDeriv r`. -/
def inSupport (M : SourceModelData) (r : ℝ) (e : Sym2 M.V) : Prop :=
  ∃ x y : M.V, x ≠ y ∧ e = s(x, y) ∧ M.S.dist x y ≤ r

end PercLib.CriticalLRP.Orchestration
