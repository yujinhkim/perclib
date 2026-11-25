/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwveg8a1`, member `m1`, direction `d4`.

Integration donor: `.ultramath/smwveg8a1/m1/Integration.lean`, verified at `cfb27572ee02f0e8dbc751b822b50389b54f2df5`.

# End-to-end assembly with `hfluxInt` supplied by direction (B)

This file combines

* `WindowMoment.lean` (member `m1`): `hmomNN`, `hmomConv` for the exact `M.windowMoment`,
  from finiteness of the second cutoff moment on the window;
* `Assembly.lean` (member `m1`): the integrated identity and the pointwise derivative with
  `hmomMono` removed entirely, `hrhsInt` derived from a bound on `M.coeffRHS`, and `hrhsCont`
  supplied by the landed off-sphere fourth-moment theorem;
* `WindowFluxBound.lean` (member `m2`, direction (B), `.ultramath/smwveg8a1/m2/`):
  `intervalIntegrable_windowFlux_family`, which is literally the `hfluxInt` input.

The resulting theorem has **no moment inputs and no `hfluxInt`**; the only hypotheses left are
the two remaining flux inputs (`hfluxMeas`, `hfluxNN`, `hfluxMono`, `hfluxConv`), the
off-corner window and monotone exhaustive window family, finiteness of the second cutoff moment
on the window and of the fourth at a strictly larger radius, the off-sphere condition at `r0`,
continuity of `M.coeffRHS` at `r0`, and a bound on `M.coeffRHS` on the window.

The imported `WindowFluxBound` module was verified separately by a strict build from its own
directory (exit 0, `#print axioms` = `[propext, Classical.choice, Quot.sound]` only).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Moment
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Assembly
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.FluxBounds

/-!
# End-to-end assembly
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **End-to-end form of the `p = 2` off-corner radius derivative.**

No moment inputs and no `hfluxInt`: `hmomMono` is eliminated, `hmomNN` and `hmomConv` are
discharged by `WindowMoment.lean`, `hrhsInt` by `intervalIntegrable_rhsScalarTwo_of_coeffBound`,
`hrhsCont` by the landed off-sphere fourth-moment theorem, and `hfluxInt` by direction (B)'s
`intervalIntegrable_windowFlux_family`. -/
theorem hasDerivAt_cutMomentReal_two_integrated {a b r0 r1 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (hfin : ∀ x ∈ Set.Icc a b, M.cutMoment 2 x ≠ ⊤)
    (hr1 : r0 < r1) (h4 : M.cutMoment 4 r1 ≠ ⊤)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0)
    (hcoefcont : ContinuousAt M.coeffRHS r0)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a r0, |M.coeffRHS r| ≤ C)
    (hfluxMeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hfluxNN : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  M.hasDerivAt_cutMomentReal_two_assembled hwin S hSmono hS har hrb hfin hr1 h4 hsphere
    hcoefcont hC0 hC hfluxMeas hfluxNN hfluxMono
    (M.intervalIntegrable_windowFlux_family S hwin) hfluxConv

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_integrated
