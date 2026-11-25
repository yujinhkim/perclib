/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.Sharpness

/-!
# The sharpness residual of the `p = 2` chain, localised to one reduced intensity

Swarm `smwvj13j4`, member `m3`, direction `d8`.

The staged `SourceWitness/Sharpness.lean` replaces the fourth-cutoff-moment hypothesis of
`hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner` by

  `hsub : ∀ β : ℝ≥0, β < M.betaCrit → ∫⁻ ω, clusterVol ω 0 ∂(M.law β) ≠ ⊤`,

i.e. by finiteness of the *uncut* first moment at **every** strictly subcritical intensity.
`hsub` is the paper's sharpness input and is not proved anywhere.  This file shows that the
chain consumes far less: **one** reduced intensity suffices, the one supplied by
Definition I.1.5 at the right endpoint of the window.

## What is proved

* `SourceModelData.cutMoment_four_ne_top_uniform_window_of_first`: for an arbitrary source
  model and every `R > 0` there is a single coefficient `c : ℝ≥0` with `0 < c < 1` such that
  finiteness of the uncut **first** moment at the single parameter `M.betaCrit * c` makes
  *every* cutoff fourth moment `M.cutMoment 4 r`, `0 < r ≤ R`, finite.  The coefficient is the
  one of `SourceModelData.exists_uniform_reduced_coefficient` (`1 − min (1/2) (K R / 2 K t₀)`,
  `t₀` the attained nonzero lattice minimum); the point is that the *quantifier order* is
  `∃ c ∀ r`, not `∀ r ∃ c`, and that the order reduction first ⟶ fourth
  (`uncutMoment_four_ne_top_of_first`) happens *after* the intensity has been lowered, so
  `hsub`'s family is never needed.
* `Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_single_reduced`: the
  nondegenerate `p = 2` off-corner derivative at an off-sphere radius `r0 ∈ (a, b)` from
  finiteness of the uncut mean at one intensity `β_c * c`, `c < 1`.
* `Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_single_reduced`: the same
  weakening for the paper's cutoff-mass derivative of Proposition I.4.2.
* `SourceModelData.lintegral_law_reduced_ne_top_of_subcritical`: `hsub` gives the single
  intensity, so these statements are at most as strong as the staged theorem — strictly
  weaker as a hypothesis bundle whenever `hsub` is only known on part of `[0, β_c)`.

## Exact remaining gap

Nothing here produces the single finiteness either.  What remains is

  `∃ c : ℝ≥0, 0 < c < 1 ∧ ∫⁻ ω, clusterVol ω 0 ∂(M.law (M.betaCrit * c)) ≠ ⊤`,

i.e. finiteness of the uncut first moment at *one explicitly given* intensity
`β_c (1 − min (1/2) (K R / 2 K t₀))` for one `R > 0` — the sharpness input of the source at a
single point of `[0, β_c)`, `β_c > 0`.  No uniform-in-`β` threshold, no critical moment, no
finite box and no percolation statement is involved.

Axiom audit at the end of the file: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. One reduced intensity bounds a whole window of fourth cutoff moments -/

/-- **One subcritical intensity bounds every fourth cutoff moment on a window.**

Finiteness of the *first* uncut moment at the single parameter `M.betaCrit * c` implies
finiteness of the fourth cutoff moment `M.cutMoment 4 r` at every `r ∈ (0, R]`.  The order
reduction first ⟶ fourth is `SourceModelData.uncutMoment_four_ne_top_of_first`, applied at the
reduced intensity (not at `β_c`), and the radius uniformity is
`SourceModelData.cutMoment_ne_top_uniform_window` at order `4`. -/
theorem SourceModelData.cutMoment_four_ne_top_uniform_window_of_first
    (M : SourceModelData) {R : ℝ} (hR : 0 < R) :
    ∃ c : NNReal, 0 < (c : ℝ) ∧ (c : ℝ) < 1 ∧
      ((∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law (M.betaCrit * c))) ≠ ⊤ →
        ∀ r : ℝ, 0 < r → r ≤ R → M.cutMoment 4 r ≠ ⊤) := by
  obtain ⟨c, hc0, hc1, hkey⟩ := M.cutMoment_ne_top_uniform_window hR 4
  exact ⟨c, hc0, hc1, fun hfin r hr0 hrR =>
    hkey (M.uncutMoment_four_ne_top_of_first hfin) r hr0 hrR⟩

/-- **The staged hypothesis `hsub` gives the single reduced intensity.**  For every `c < 1`
the parameter `M.betaCrit * c` is strictly subcritical as soon as `M.betaCrit > 0`, so the
family of the staged file implies each individual instance.  Hence every statement below is
at most as strong as the staged theorem. -/
theorem SourceModelData.lintegral_law_reduced_ne_top_of_subcritical (M : SourceModelData)
    (hβ : 0 < M.betaCrit)
    (hsub : ∀ β : NNReal, β < M.betaCrit →
      (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law β)) ≠ ⊤)
    {c : NNReal} (hc : (c : ℝ) < 1) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law (M.betaCrit * c))) ≠ ⊤ := by
  have hlt : M.betaCrit * c < M.betaCrit := by
    have h : M.betaCrit * c < M.betaCrit * 1 :=
      mul_lt_mul_of_pos_left (by rwa [← NNReal.coe_lt_coe, NNReal.coe_one]) hβ
    simpa using h
  exact hsub _ hlt

/-! ## 2. The `p = 2` off-corner derivative from one reduced intensity -/

namespace Witness

/-- **The nondegenerate `p = 2` off-corner derivative from one reduced intensity.**

The window hypothesis `∀ t ∈ Ioc a b, M.cutMoment 4 t ≠ ⊤` of
`hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner` is discharged from the single
finiteness `∫⁻ clusterVol 0 ∂(M.law (β_c * c)) ≠ ⊤` with `c < 1`, at the coefficient supplied
by `cutMoment_four_ne_top_uniform_window_of_first` on `(0, b]`.  In particular the whole
subcritical family `hsub` is *not* consumed. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_single_reduced
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {a b r0 : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (har : a < r0) (hrb : r0 < b)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0) :
    ∃ c : NNReal, 0 < (c : ℝ) ∧ (c : ℝ) < 1 ∧
      ((∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
          ∂((sourceModelWitness d hd α hα).law ((sourceModelWitness d hd α hα).betaCrit * c)))
        ≠ ⊤ →
        HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
          (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
            * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0) := by
  have hb : 0 < b := lt_trans (lt_trans hwin.1 har) hrb
  obtain ⟨c, hc0, hc1, hkey⟩ :=
    (sourceModelWitness d hd α hα).cutMoment_four_ne_top_uniform_window_of_first hb
  exact ⟨c, hc0, hc1, fun hfin =>
    hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner d hd α hα hwin har hrb
      (fun t ht => hkey hfin t (lt_trans hwin.1 ht.1) ht.2) hsphere⟩

/-- **The paper's cutoff-mass derivative from one reduced intensity.**

The radius `R := r0 + 1` is strictly larger than `r0`, so the same single-intensity input
supplies the finite first cutoff moment `M.cutMoment 1 (r0 + 1)` that
`sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_firstMoment` consumes. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_single_reduced
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r0 : ℝ} (hr0 : 0 < r0)
    (hoff : r0 ∉ (sourceModelWitness d hd α hα).cornerRadii) :
    ∃ c : NNReal, 0 < (c : ℝ) ∧ (c : ℝ) < 1 ∧
      ((∫⁻ ω, clusterVol ω (0 : (sourceModelWitness d hd α hα).V)
          ∂((sourceModelWitness d hd α hα).law ((sourceModelWitness d hd α hα).betaCrit * c)))
        ≠ ⊤ →
        HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
          (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
            (sourceModelWitness d hd α hα).exclScalar r0) r0) := by
  obtain ⟨c, hc0, hc1, hkey⟩ :=
    (sourceModelWitness d hd α hα).cutMoment_four_ne_top_uniform_window_of_first
      (R := r0 + 1) (by linarith)
  refine ⟨c, hc0, hc1, fun hfin => ?_⟩
  have h1R : (sourceModelWitness d hd α hα).cutMoment 1 (r0 + 1) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hkey hfin (r0 + 1) (by linarith) le_rfl) ?_
    exact lintegral_mono fun ω => pow_le_pow_right₀
      (SourceModelData.one_le_clusterVol ω (0 : (sourceModelWitness d hd α hα).V))
      (by norm_num)
  exact sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_firstMoment d hd α hα
    hr0 (by linarith) hoff h1R

end Witness

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_four_ne_top_uniform_window_of_first
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.lintegral_law_reduced_ne_top_of_subcritical
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_offCorner_of_single_reduced
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_single_reduced
