/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Continuity in the cutoff radius of the forced connection probabilities and the pivotal flux.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.MixedFluxDensityMonotone
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.ForcedContinuity

/-!
# Continuity of the forced connection probabilities and of the fixed-edge pivotal flux

* `SourceModelData.continuousAt_forcedEvent`: for a fixed edge `e` forced to the state `η`,
  the probability that the origin is connected to `y` is continuous in the cutoff radius at
  every positive radius with finite first cutoff moment at a larger radius.
* `SourceModelData.continuousAt_pivotalFlux_singleton`: the pivotal flux of a fixed edge `e`
  for the cluster indicator of `y` is continuous in the cutoff radius, because it is the
  difference of the forced-open and forced-closed probabilities
  (`integral_flipDiff_indicator`).

Both are unconditional in the off-corner sense: no off-corner hypothesis appears, and the
only moment input is `M.cutMassAt r₁ 0 ≠ ⊤` for one `r₁ > r₀`, which is implied by
finiteness of the second cutoff moment at `r₁`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Continuity of a forced connection probability in the cutoff radius.** -/
theorem continuousAt_forcedEvent {r0 r1 : ℝ} (hr0 : 0 < r0) (hr01 : r0 < r1)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) (e : Sym2 M.V) (η : Config M.V) {a b : M.V}
    (hab : e = s(a, b)) (hη : ∀ f : Sym2 M.V, f ∈ η → f = e) (y : M.V) :
    ContinuousAt (fun r : ℝ =>
      (M.cutLaw r).real ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
        {σ : Config M.V | Connects σ (0 : M.V) y})) r0 := by
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  obtain ⟨N, hN⟩ := M.exists_escapeForce_lt e η hη hab hfin (ε := ε / 8) (by linarith)
  have hevbox : ∀ᶠ r : ℝ in 𝓝 r0,
      (∑ f ∈ M.boxEdges (N : ℝ), |(M.cutProb r f : ℝ) - (M.cutProb r0 f : ℝ)|) < ε / 8 :=
    (M.tendsto_sum_abs_cutProb hr0 (M.boxEdges (N : ℝ))).eventually
      (Iio_mem_nhds (by linarith))
  have hevpos : ∀ᶠ r : ℝ in 𝓝 r0, 0 < r ∧ r ≤ r1 := by
    have h1 : ∀ᶠ r : ℝ in 𝓝 r0, 0 < r := isOpen_Ioi.eventually_mem hr0
    have h2 : ∀ᶠ r : ℝ in 𝓝 r0, r < r1 := isOpen_Iio.eventually_mem hr01
    exact h1.and (h2.mono fun r h => le_of_lt h)
  filter_upwards [hevbox, hevpos] with r hbox hpos
  have hesc1 : (M.cutLaw r).real (M.escapeForce e η (N : ℝ)) ≤ ε / 8 :=
    le_trans (M.escapeForce_real_mono hpos.1 (hr0.trans hr01) hpos.2 e η)
      (le_of_lt (hN N le_rfl))
  have hesc0 : (M.cutLaw r0).real (M.escapeForce e η (N : ℝ)) ≤ ε / 8 :=
    le_trans (M.escapeForce_real_mono hr0 (hr0.trans hr01) hr01.le e η)
      (le_of_lt (hN N le_rfl))
  have hmain := M.forcedEvent_abs_sub_le e η y r r0 (N : ℝ)
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hmain ?_
  linarith

/-- **Continuity of the fixed-edge pivotal flux of the cluster indicator.** -/
theorem continuousAt_pivotalFlux_singleton {r0 r1 : ℝ} (hr0 : 0 < r0) (hr01 : r0 < r1)
    (hfin : M.cutMassAt r1 0 ≠ ⊤) (y : M.V) (e : Sym2 M.V) :
    ContinuousAt (fun r : ℝ => pivotalFlux (edgeMeasure (M.cutProb r))
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) r0 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    have hE : MeasurableSet {σ : Config M.V | Connects σ (0 : M.V) y} :=
      measurableSet_connects (0 : M.V) y
    have hcongr : ∀ r : ℝ, pivotalFlux (edgeMeasure (M.cutProb r))
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) s(a, b)
        = (M.cutLaw r).real (M.rawOpenEvent s(a, b) {σ : Config M.V | Connects σ (0 : M.V) y})
          - (M.cutLaw r).real
              (M.rawClosedEvent s(a, b) {σ : Config M.V | Connects σ (0 : M.V) y}) := by
      intro r
      have h := M.integral_flipDiff_indicator (M.cutLaw r) s(a, b) hE
      rw [show sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)
          = {σ : Config M.V | Connects σ (0 : M.V) y}.indicator (fun _ => (1 : ℝ)) from by
        rw [M.sMomentTrunc_singleton_as_indicator y]
        rfl]
      exact h
    have hopen := M.continuousAt_forcedEvent hr0 hr01 hfin s(a, b) ({s(a, b)} : Config M.V)
      rfl (fun f hf => by simpa using hf) y
    have hclosed := M.continuousAt_forcedEvent hr0 hr01 hfin s(a, b) (∅ : Config M.V)
      rfl (fun f hf => by simp at hf) y
    refine (hopen.sub hclosed).congr ?_
    filter_upwards with r
    exact (hcongr r).symm

/-- **Finiteness of the first cutoff moment from finiteness of the second.** -/
theorem continuousAt_pivotalFlux_singleton_of_cutMoment {r0 : ℝ} (hr0 : 0 < r0) {β : ℝ}
    (hr0β : r0 < β) (h2 : M.cutMoment 2 β ≠ ⊤) (y : M.V) (e : Sym2 M.V) :
    ContinuousAt (fun r : ℝ => pivotalFlux (edgeMeasure (M.cutProb r))
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) r0 := by
  have hfin : M.cutMassAt β 0 ≠ ⊤ := by
    rw [M.cutMassAt_zero_eq_cutMoment]
    exact M.cutMoment_one_ne_top_of_two h2
  exact M.continuousAt_pivotalFlux_singleton hr0 hr0β hfin y e

end SourceModelData

end PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.cluster_forceOn_singleton_subset
#print axioms SourceModelData.escapeForce_subset
#print axioms SourceModelData.exists_escapeForce_lt
#print axioms SourceModelData.forcedEvent_abs_sub_le
#print axioms SourceModelData.continuousAt_forcedEvent
#print axioms SourceModelData.continuousAt_pivotalFlux_singleton
#print axioms SourceModelData.continuousAt_pivotalFlux_singleton_of_cutMoment
