/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvdggcc`, member `m1`, direction `d3`.

Integration donor: `.ultramath/smwvdggcc/m1`; independently checked at `0b87f45527ec4090b7f9189ab48f7ade24cac41e`.

# Window objects for the integrated `p = 2` radius identity

The swarm target is, at an off-sphere radius `r0 > 0`,

`HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0`,

with `M.rhsScalarTwo r = M.coeffRHS r * (M.p2RHS r).toReal` the accepted `p = 2` right-hand
side of Hutchcroft, *Critical long-range percolation I*, Lemma I.4.1.

This file introduces only the three objects needed to *integrate* the radius identity against
the radius variable, and the window predicate on which all radii are off the corner set:

* `clusterVolSqReal` — the observand `|K_0|^2` of `cutMomentReal 2` as a real function;
* `windowMoment` — the expectation of its restriction to a finite edge window, i.e. the
  finite-window primitive whose radius derivative is the unconditional finite Russo identity
  `Deriv.hasDerivAt_integral_cutFun_cutLaw`;
* `windowFlux` — that finite-window derivative, the finite pivotal sum;
* `IsWindowMajorantOn` — a bound on a family of radius functions by one fixed radius function,
  used for dominated convergence in the window index rather than window-index monotonicity.

The original window objects are defined here; the monotone-free exchange and its model-level
FTC are in `Exchange.lean` and `RadiusFTC.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Flux.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.WindowExchange.Defs

/-!
# Window moment and window flux of the squared cluster volume
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

/-- The square of the cut-off cluster volume of the origin, as a real-valued function of the
configuration: the observand of `M.cutMomentReal 2`. -/
noncomputable def clusterVolSqReal : Config M.V → ℝ :=
  SecondMomentExchange.volSq (0 : M.V)

/-- The a.e. equality of the observand with the `ℝ≥0∞` square, on the `ℝ≥0∞` side on which the
finite-window Russo identity is proved.  Definition unfolding only. -/
theorem clusterVolSqReal_apply (ω : Config M.V) :
    M.clusterVolSqReal ω = (clusterVol ω (0 : M.V)).toReal ^ 2 := rfl

/-- The **window moment**: the expectation, under the cut-off law at radius `r`, of the square
of the cluster volume of the origin computed inside the finite edge window `S`.

This is the quantity whose radius derivative is the finite pivotal sum `windowFlux`, by the
unconditional Russo identity of `Deriv.hasderivAt_integral_cutFun_cutLaw`; it increases to
`M.cutMomentReal 2` as the window exhausts the edge set. -/
noncomputable def windowMoment (S : Finset (Sym2 M.V)) (r : ℝ) : ℝ :=
  ∫ ω, cutFun S M.clusterVolSqReal ω ∂(M.cutLaw r)

/-- The **window flux**: the finite pivotal sum of the window moment, i.e. the derivative of
`M.windowMoment S` in the radius at every off-corner radius. -/
noncomputable def windowFlux (S : Finset (Sym2 M.V)) (r : ℝ) : ℝ :=
  ∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e

/-- A closed radius window `[a, b]` on which the off-corner hypothesis holds at *every* point:
every radius is positive and no radius of the window is the `ρ`-length of an edge.  This is the
set of radii at which the edge probability is differentiable with the source weight
`cutEdgeDeriv` (`hasDerivAt_cutProb_off`), so that the finite-window Russo identity can be
integrated over the whole window. -/
def IsOffCornerWindow (a b : ℝ) : Prop :=
  0 < a ∧ a ≤ b ∧ ∀ r ∈ Set.Icc a b, r ∉ M.cornerRadii

end SourceModelData

/-- A family `F n` of radius functions is dominated on `s` by one fixed radius function `G`.
This hypothesis concerns only uniformity in the window index, not ordering of the windows. -/
def IsWindowMajorantOn (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ n, ∀ t ∈ s, F n t ≤ G t

/-- On a nonnegative family, a one-sided majorant is a norm majorant suitable for dominated
convergence. -/
theorem IsWindowMajorantOn.norm_le {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {s : Set ℝ}
    (h : IsWindowMajorantOn F G s) (hnn : ∀ n t, 0 ≤ F n t) {n : ℕ} {t : ℝ} (ht : t ∈ s) :
    ‖F n t‖ ≤ G t := by
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn n t)]
  exact h n t ht

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.clusterVolSqReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowFlux
#print axioms PercLib.CriticalLRP.Orchestration.IsWindowMajorantOn
#print axioms PercLib.CriticalLRP.Orchestration.IsWindowMajorantOn.norm_le
