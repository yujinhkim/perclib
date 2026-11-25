/-
# The per-`(y,e)` summand of the standardized off-corner excluded flux

Swarm `smwudd7jf`, member `m1`, direction **D1B** (assembly of the off-corner Russo derivative
from the already-proved pieces).  Nothing here is added to the production tree.

Two objects of the existing tree are used throughout:

* `sMomentInfFlux 0 {y} 1 M.cutProb M.cutEdgeDeriv r` — the `y`-th summand of the vertex series
  whose `tsum` is the derivative value produced by
  `SourceModelData.hasDerivAt_cutMassReal_tsum_sMomentInfFlux`; by
  `sMomentInfFlux_eq_tsum_pairIncrFlux` it is *literally* `∑'_e cutEdgeDeriv r e *
  pivotalFlux (cutLaw r) (sMomentTrunc 1 0 {y}) e`;
* `∑ e ∈ X.sym2, cutEdgeDeriv r e * pivotalFlux (cutLaw r) (sMomentTrunc 1 0 A) e` — the
  finite-window standardized excluded flux of
  `SourceModelData.sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr`, whose cofinal limit is
  `β_c (-K'(r)) (exclMass r).toReal` by `tendsto_sum_cutEdgeDeriv_mul_pivotalFlux`.

The two differ only in the order of summation: the vertex series fixes `A = {y}` and sums over
`e`, the excluded-flux series fixes a window `X` of edges and sums over a *truncation* `A`.  The
definition below names the common summand so that both can be written as sums of one function of
the pair `(y, e)`, and the two orders can be compared by `Summable.tsum_comm`.

No proof, no measure and no derivative enters: this is a definition layer.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.RussoAssembly.Main

/-!
# The per-vertex and per-edge excluded-flux summand

This module defines `pairFlux`. Additivity of truncated pivotal fluxes and the excluded-flux
assembly are proved in `RussoExcluded.Main`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The summand shared by the vertex series of the off-corner cut-mass derivative and the
finite-window standardized excluded flux: the cutoff-derivative weight of the edge `e` times the
pivotal flux of the singleton two-point functional `1{y ∈ K_0}` through `e`, both at radius `r`. -/
noncomputable def pairFlux (r : ℝ) (y : M.V) (e : Sym2 M.V) : ℝ :=
  M.cutEdgeDeriv r e *
    pivotalFlux (M.cutLaw r)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit of the definition -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairFlux

end PercLib.CriticalLRP.Orchestration
