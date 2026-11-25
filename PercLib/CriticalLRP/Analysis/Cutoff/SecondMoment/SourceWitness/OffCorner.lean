/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvi25ua`, member `m2`, direction `d2`, composition with direction `d1`.

# The witness radius derivative, composed from both swarm directions

This file composes the two directions of the swarm and obtains (i) the derivative on `[1/2, 1]` with
*no* hypotheses, and (ii) the nondegenerate derivative at an arbitrary off-sphere radius with the
majorant *discharged*, leaving only finiteness of the fourth cutoff moment on `(a, b]`:

* `OffCornerAssembly.lean` (m2, direction `d2`) — the radius assembly: the monotone-free
  `hfluxConv` from the fourth cutoff moment, the window-local dominated convergence, and the
  reduction of `HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0` to a
  uniform-in-window majorant plus its interval integrability;
* `WindowMajorant/{Defs,Main,Witness}.lean` (m1, direction `d1`) — the majorant itself,
  `M.windowMajorant C b t = 2 * (M.rhsScalarTwo t + 3 C (M.cutMoment 4 b).toReal)`, its pointwise
  domination of the window fluxes and its interval integrability.

Composing them on the canonical box windows and the off-corner window `[1/2, 1]` gives

`HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
  (powLawCoeff β_c d α r0 * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0`

for `1/2 < r0 < 1`, `1 ≤ d`, `0 < α`, with **no further hypothesis**: the fourth cutoff moment on
`(0, 1]` is `1` (`cutMoment_sourceModelWitness_eq_one`), so both the pointwise majorant
(`hfluxMaj_boxEdges`) and its interval integrability (via `intervalIntegrable_candidateMajorant`
with a.e. strong measurability from the window-flux convergence on `(1/2, 1]`) are unconditional.

## The nondegenerate case is in §2, and it also needs no majorant

`[1/2, 1]` lies below radius `2`, where the witness cut kernel vanishes identically: there
`M.cutLaw r` is the point mass at the empty configuration, `M.cutMoment p r = 1` and
`M.p2RHS r = 0`, so the derivative value of §1 is `0`.  That is the **degenerate** small-radius
regime; §1 is an end-to-end check of the composed machinery.

§2 is the substantive statement.  Direction `d1`'s majorant works on *any* off-corner window
`[a, b]` once `M.cutMoment 4 b ≠ ⊤` and the coefficient bound hold, so it can be fed to direction
`d2`'s assembly at an arbitrary window.  The result,

`Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner`,

is the off-corner radius derivative at an **arbitrary positive off-sphere radius** `r0 ∈ (a, b)`, with
the majorant *discharged*, and with exactly one remaining hypothesis:

  `∀ t ∈ Ioc a b, M.cutMoment 4 t ≠ ⊤`.

That hypothesis is genuine above radius `2` (the witness cut law is not the Dirac law there, and
`M.cutLaw t` differs with `t`, so finiteness at `b` does not give finiteness at `t < b`), and it is
not derived here.  `Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_three_and_seven_unconditional`
is the concrete instance at `r0 = 37/10` on `[7/2, 39/10]`, with the off-corner and off-sphere
conditions discharged, again conditional only on the fourth moment on `(7/2, 39/10]`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.LocalFTC
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.WindowMajorant.Witness

/-!
# The composed, unconditional small-radius witness derivative
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

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-- The window-flux convergence on `(1/2, 1]` at the witness, from `M.cutMoment 4 t = 1` for
`t < 2`.  No `∀ t > 0` hypothesis is needed: `tendsto_windowFlux_of_cutMoment_four` is applied at each
radius separately. -/
theorem tendsto_windowFlux_boxEdges_Ioc (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t) atTop
        (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t)) := by
  intro t ht
  exact (sourceModelWitness d hd α hα).tendsto_windowFlux_of_cutMoment_four t
    (lt_trans (by norm_num) ht.1)
    (cutMoment_four_sourceModelWitness d hd α hα
      (lt_of_le_of_lt ht.2 (show (1 : ℝ) < 2 by norm_num)))
    (boxEdges d) (boxEdges_mono d) (exists_mem_boxEdges d)

/-- Interval integrability of the witness majorant on `[1/2, 1]`, without any global measurability
hypothesis: a.e. strong measurability on the window suffices. -/
theorem intervalIntegrable_windowMajorant_boxEdges (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    IntervalIntegrable
      ((sourceModelWitness d hd α hα).windowMajorant (witnessCoeffConst d hd α hα) 1)
      volume (1 / 2) 1 := by
  have hAE : AEStronglyMeasurable (fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t)
      (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact (sourceModelWitness d hd α hα).aeStronglyMeasurable_rhsScalarTwo_restrict
      (boxEdges d) (tendsto_windowFlux_boxEdges_Ioc d hd α hα)
  have hfun : ((sourceModelWitness d hd α hα).windowMajorant (witnessCoeffConst d hd α hα) 1)
      = fun t => 2 * ((sourceModelWitness d hd α hα).rhsScalarTwo t
          + 3 * witnessCoeffConst d hd α hα
            * ((sourceModelWitness d hd α hα).cutMoment 4 1).toReal) := rfl
  rw [hfun]
  exact (sourceModelWitness d hd α hα).intervalIntegrable_candidateMajorant
    (a := 1 / 2) (b := 1) (C := witnessCoeffConst d hd α hα)
    (by norm_num) hAE (witnessCoeffConst_nonneg d hd α hα)
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le_witnessCoeffConst d hd α hα hr)
    (cutMoment_four_one_sourceModelWitness d hd α hα)

/-- **The `p = 2` radius derivative at the source power law on `[1/2, 1]`, with no hypotheses.**

This is the composition of direction `d2` (the assembly) with direction `d1` (the majorant), and the
first end-to-end instance in which *every* hypothesis has been discharged.  It is the degenerate
small-radius case: `[1/2, 1]` is below radius `2`, where the witness cut kernel vanishes and the
derivative value is `0`. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_box_unconditional
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r0 : ℝ}
    (hr0lo : 1 / 2 < r0) (hr0hi : r0 < 1) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_box_noMoments_majorant d hd α hα hr0lo hr0hi
    (hfluxMaj_boxEdges d hd α hα) (intervalIntegrable_windowMajorant_boxEdges d hd α hα)


/-! ## 2. The nondegenerate case: the majorant discharged by direction `d1` on an arbitrary window

The block above only composes the two directions on `[1/2, 1]`, where the majorant is free because
the model is the Dirac law.  The composition works at *any* off-corner window: direction `d1`'s
`windowFlux_le_windowMajorant_of_cutMoment_four_le` gives the pointwise majorant from
`M.cutMoment 4 b ≠ ⊤` and the coefficient bound alone, and direction `d2`'s
`intervalIntegrable_candidateMajorant` gives its interval integrability from a.e. strong
measurability.  The result below therefore has **no majorant hypothesis at all**.

What remains is exactly the analytic input that is *not* available at the witness: finiteness of the
fourth cutoff moment on `(a, b]`.  Above radius `2` the witness cut law is not the Dirac law, so
this is a genuine hypothesis, not a formality, and it is not derived from finiteness at `b`
(`M.cutLaw t` is a different measure for every `t`). -/

/-- **The witness off-corner radius derivative at an arbitrary off-sphere radius, with the
majorant discharged.**

Inputs: an off-corner window `[a, b]` with `a < r0 < b`, the off-sphere condition at `r0`, and
finiteness of the fourth cutoff moment on `(a, b]`.  Conclusion: the derivative of the second cutoff
moment is the paper's `powLawCoeff β_c d α r0 * (p2RHS r0)ᵗᵒᴿᵉᵃˡ`.

No `hfluxMono`, no global measurability of `M.rhsScalarTwo`, no finite box, no two-sided claim at an
attained radius, and no `toReal` of an infinite moment.  The convergence `hfluxConv` is applied at
each radius `t ∈ (a, b]` separately (`tendsto_windowFlux_of_cutMoment_four`), so the fourth moment is
required only where it is actually used. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b r0 : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (har : a < r0) (hrb : r0 < b)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc a b →
      (sourceModelWitness d hd α hα).cutMoment 4 t ≠ ⊤)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 := by
  have ha : 0 < a := hwin.1
  have hab : a ≤ b := hwin.2.1
  have hb : 0 < b := lt_trans (lt_trans ha har) hrb
  have h4b : (sourceModelWitness d hd α hα).cutMoment 4 b ≠ ⊤ :=
    h4 b ⟨lt_trans har hrb, le_rfl⟩
  -- the coefficient bound of the witness on `[a, b]`, from the exact power law
  have hC0 : 0 ≤ powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a :=
    powLawCoeffBound_nonneg (d := d) (α := α) (β := _) ha
  have hC : ∀ r ∈ Set.Icc a b,
      |(sourceModelWitness d hd α hα).coeffRHS r|
        ≤ powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a :=
    fun _ hr => abs_coeffRHS_sourceModelWitness_le d hd α hα ha hr.1
  -- the flux convergence on `(a, b]`, radius by radius
  have hfluxConv : ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t) atTop
        (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t)) := by
    intro t ht
    exact (sourceModelWitness d hd α hα).tendsto_windowFlux_of_cutMoment_four t
      (lt_trans ha ht.1) (h4 t ht)
      (boxEdges d) (boxEdges_mono d) (exists_mem_boxEdges d)
  -- the majorant, from direction `d1`
  have hfluxMaj :
      IsWindowMajorantOn
        (fun n => (sourceModelWitness d hd α hα).windowFlux (boxEdges d n))
        ((sourceModelWitness d hd α hα).windowMajorant
          (powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a) b)
        (Set.Ioc a b) :=
    (sourceModelWitness d hd α hα).windowFlux_le_windowMajorant_of_cutMoment_four_le
      (a := a) (b := b) (C := powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a)
      ha hab h4b hC0 hC (boxEdges d)
  -- its interval integrability, with a.e. strong measurability on the window
  have hAE : AEStronglyMeasurable (fun t => (sourceModelWitness d hd α hα).rhsScalarTwo t)
      (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact (sourceModelWitness d hd α hα).aeStronglyMeasurable_rhsScalarTwo_restrict
      (boxEdges d) hfluxConv
  have hG : IntervalIntegrable
      ((sourceModelWitness d hd α hα).windowMajorant
        (powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a) b)
      volume a b := by
    have hfun :
        ((sourceModelWitness d hd α hα).windowMajorant
          (powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a) b)
        = fun t => 2 * ((sourceModelWitness d hd α hα).rhsScalarTwo t
            + 3 * powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a
              * ((sourceModelWitness d hd α hα).cutMoment 4 b).toReal) := rfl
    rw [hfun]
    exact (sourceModelWitness d hd α hα).intervalIntegrable_candidateMajorant
      (a := a) (b := b) (C := powLawCoeffBound ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α a)
      hab hAE hC0 hC h4b
  exact hasDerivAt_cutMomentReal_two_sourceModelWitness_majorant d hd α hα hwin (boxEdges d)
    (boxEdges_mono d) (exists_mem_boxEdges d) har hrb h4 hsphere hfluxMaj hG

/-- **The nondegenerate derivative at the concrete radius `r0 = 37/10`**, with every hypothesis
except the fourth-moment finiteness discharged: the window `[7/2, 39/10]` is off corner, `37/10` is
off sphere, and the majorant is supplied by direction `d1`.  `37/10 > 2`, so the cut law there is
not the Dirac law at the empty configuration. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_three_and_seven_unconditional
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc (7 / 2 : ℝ) (39 / 10) →
      (sourceModelWitness d hd α hα).cutMoment 4 t ≠ ⊤) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α (37 / 10)
        * ((sourceModelWitness d hd α hα).p2RHS (37 / 10)).toReal) (37 / 10) :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα
    (isOffCornerWindow_sourceModelWitness_seven_halves d hd α hα)
    (by norm_num) (by norm_num) h4
    (sourceModelWitness_sphere_ne_seven_tenths d hd α hα)

end PercLib.CriticalLRP.Orchestration.Witness

end

/-! ## Axiom audit -/

#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.tendsto_windowFlux_boxEdges_Ioc
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.intervalIntegrable_windowMajorant_boxEdges
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_box_unconditional
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_three_and_seven_unconditional
