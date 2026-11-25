/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwveg8a1`, member `m3`, direction (C).

Integration donor: `.ultramath/smwveg8a1/m3/FluxConv`; independently checked at `cfb27572ee02f0e8dbc751b822b50389b54f2df5`.

# Fixed-radius window-flux vocabulary for the integrated `p = 2` identity

The swarm target is the pointwise off-corner `p = 2` radius derivative
`HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0`, whose landed
orchestration `SourceModelData.hasDerivAt_cutMomentReal_two` consumes, at a fixed radius,
the pointwise-in-`r` convergence of the finite-window pivotal sums

`M.windowFlux (S k) r = ∑ e ∈ S k, M.cutEdgeDeriv r e · (pivotalFlux of the windowed square)`

to the accepted right-hand side `M.rhsScalarTwo r`.  This file introduces only the objects that
split that convergence into a part that is *summation theory* and a part that is the paper's
insertion tolerance:

* `partialLimitFlux S r` — the same edge sum but with the **untruncated** pivotal flux
  `pivotalFlux (M.cutLaw r) |K₀|² e`, i.e. the product of the fixed-radius FLUX identity
  `tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo` truncated to the window `S`;
* `windowClosedGhost S r e` — the mean, under `M.cutLaw r`, of the exact nonnegative
  `ℝ≥0∞` closed ghost `quadEdgeWeight` evaluated at the **windowed** configuration
  `cutConfig S ω`, i.e. the finite-window counterpart of the landed per-edge identity
  `SourceModelData.cutEdgeClosedWeight_mul_pivotalFlux_eq`;
* `insertionDeficit`/`insertionError` — the difference between the windowed and untruncated
  pivotal fluxes summed against the source's coefficients, in signed and in absolute-value
  form.  The absolute-value form is the `p = 2` instance of the paper's insertion error
  `SecondMomentExchange.insertionFlux`.

No mathematical statement is asserted here; every theorem is in `Main.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Flux.PerEdge

/-!
# Fixed-radius window flux vocabulary
-/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The range predicate of the cutoff at the fixed radius `r`, in the argument order used by
`quadPairWeight` (`dt c b` means "`c` is within `r` of `b`"). -/
def cutRange (r : ℝ) : M.V → M.V → Prop := fun c b => M.S.dist c b ≤ r

/-- **The truncated infinite pivotal flux**: the fixed-radius FLUX edge sum of
`tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo`, cut down to the finite window `S`.

This is *not* `M.windowFlux S r`: the pivotal flux here is the one of the untruncated square
`|K₀|²`, while `windowFlux` uses the pivotal flux of the windowed observable `cutFun S |K₀|²`.
The two differ by `insertionDeficit`. -/
noncomputable def partialLimitFlux (S : Finset (Sym2 M.V)) (r : ℝ) : ℝ :=
  ∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) M.clusterVolSqReal e

/-- **The finite-window closed ghost**: the `M.cutLaw r`-mean of the exact nonnegative
`ℝ≥0∞` quadratic edge weight `quadEdgeWeight` evaluated at the windowed configuration
`cutConfig S ω`.

For `e ∈ S` this is the finite-window counterpart of the landed per-edge identity
`cutEdgeClosedWeight r e · pivotalFlux (M.cutLaw r) |K₀|² e = ∫ quadEdgeWeight (·)`,
with the unbounded square replaced by the windowed square; unlike the untruncated identity it
needs no finiteness of the first cutoff moment, because every cluster volume of `cutConfig S ω`
is finite. -/
noncomputable def windowClosedGhost (S : Finset (Sym2 M.V)) (r : ℝ) (e : Sym2 M.V) : ℝ :=
  ∫ ω, (quadEdgeWeight (M.cutRange r) (cutConfig S ω) (0 : M.V) e).toReal ∂(M.cutLaw r)

/-- **The insertion deficit of a window**: the signed difference between the untruncated and the
windowed pivotal fluxes, summed against the source's edge coefficients on the window. -/
noncomputable def insertionDeficit (S : Finset (Sym2 M.V)) (r : ℝ) : ℝ :=
  ∑ e ∈ S, M.cutEdgeDeriv r e *
    (pivotalFlux (M.cutLaw r) M.clusterVolSqReal e -
      pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e)

/-- **The insertion error of a window** in absolute-value form: the `p = 2` instance of
`SecondMomentExchange.insertionFlux`.  It dominates `|insertionDeficit|`, so its vanishing along an
exhausting family implies `hfluxConv`. -/
noncomputable def insertionError (S : Finset (Sym2 M.V)) (r : ℝ) : ℝ :=
  ∑ e ∈ S, |M.cutEdgeDeriv r e| *
    |pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e -
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e|

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutRange
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.partialLimitFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowClosedGhost
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.insertionDeficit
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.insertionError
