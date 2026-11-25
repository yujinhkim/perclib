/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The closed-coordinate `(1 - q_e)` factorization for `L¹` observations

Swarm `smwvctsvt`, member `m1`, direction `d3` (route A of the brief).

Integrated from the isolated draft `.scratch/verification/smwvctsvt-m1-current/ClosedL1.lean`,
with coordinator API repairs and strict verification at `325a48e122d693325e2d43172c26a0603650fd9a`.

The landed theorem `PercLib.CriticalLRP.Orchestration.one_sub_mul_pivotalFlux_eq`
(`Analysis/Cutoff/ExcludedFlux.lean`) proves, for a *bounded* measurable observation `g`,

`(1 - q_e) * pivotalFlux μ g e = ∫ ω, 1{e ∉ ω} · (g (ω ∪ {e}) - g ω) ∂μ`,

`μ` being the independent-edge Bernoulli law.  The paper's `p = 2` target needs this identity
for the *unbounded* observation `g ω = |K_0 ω|²`, so the boundedness hypothesis has to be
replaced by something that survives at infinite cluster volume.

This file replaces it by integrability of `g` at the **two pinned laws**

`μ₁ = law (update π e 1)`  (edge `e` forced open)  and  `μ₀ = law (update π e 0)`
(edge `e` forced closed),

which is the exact input: the two terms `g (ω ∪ {e})` and `g (ω \ {e})` inside the flip
difference `flipDiff g e` are the two coordinate modifications, and each is integrable against
the ambient law exactly when `g` is integrable against the corresponding pinned law.  Nothing
else is used: no boundedness, no moment hypothesis on a model, no domination, no
`toReal`-of-`⊤` convention.  The degenerate values `q_e = 0` and `q_e = 1` are *not* case-split:
at `q_e = 1` the factor `1 - q_e` vanishes, at `q_e = 0` the closed event has full measure;
both are instances of one proof, since the law itself is the one that collapses onto the
corresponding pinned law.

The three results, from weakest to strongest input:

* `integral_compl_indicator_mul_of_sdiff_determined_of_integrable` — the single-coordinate
  factorization for an integrable `sdiff`-determined `G`, the `L¹` form of the landed
  nonnegativity-only `integral_compl_indicator_mul_of_sdiff_determined`;
* `pivotalFlux_eq_integral_pinned` — the flip mean is the *difference of the two pinned
  expectations*, `pivotalFlux μ g e = ∫ g dμ₁ - ∫ g dμ₀`;
* `one_sub_mul_pivotalFlux_eq_of_integrable` — the closed-event factorization for `L¹` `g`.

Nothing here mentions the source model, a radius, a derivative or an edge sum.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux
public import PercLib.Probability.Coordinate

/-!
# Closed-coordinate factorization for integrable observations

The bounded hypothesis of `one_sub_mul_pivotalFlux_eq` is replaced by integrability at the two
single-coordinate pinned laws, which is exactly what the two coordinate modifications of
`flipDiff` consume.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.hashCommand false
set_option linter.style.longLine false

open MeasureTheory Set
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. The two coordinate modifications as pushforwards -/

/-- Forcing the edge `e` open moves the Bernoulli law to the pinned law `update π e 1`. -/
theorem map_union_singleton_law (π : Sym2 V → unitInterval) (e : Sym2 V) :
    Measure.map (fun ω : Config V => ω ∪ {e}) (PercLib.Percolation.Bond.law π)
      = PercLib.Percolation.Bond.law (Function.update π e 1) := by
  have hfun : (fun ω : Config V => ω ∪ {e}) = fun ω => insert e ω := by
    funext ω
    rw [Set.insert_eq, Set.union_comm]
  rw [hfun]
  exact PercLib.Probability.prodBernoulli_map_insert π e

/-- Forcing the edge `e` closed moves the Bernoulli law to the pinned law `update π e 0`. -/
theorem map_sdiff_singleton_law (π : Sym2 V → unitInterval) (e : Sym2 V) :
    Measure.map (fun ω : Config V => ω \ {e}) (PercLib.Percolation.Bond.law π)
      = PercLib.Percolation.Bond.law (Function.update π e 0) :=
  PercLib.Probability.prodBernoulli_map_diff_singleton π e

/-- The expectation of `g` composed with "force `e` open" is the expectation of `g` under the
pinned-open law.  No integrability is needed: this is `integral_map`, an identity. -/
theorem integral_comp_union_singleton (π : Sym2 V → unitInterval) (e : Sym2 V)
    {g : Config V → ℝ} (hg : Measurable g) :
    ∫ ω, g (ω ∪ {e}) ∂(PercLib.Percolation.Bond.law π)
      = ∫ ω, g ω ∂(PercLib.Percolation.Bond.law (Function.update π e 1)) := by
  rw [← map_union_singleton_law π e,
    MeasureTheory.integral_map (measurable_union_singleton e).aemeasurable
      hg.aestronglyMeasurable]

/-- The expectation of `g` composed with "force `e` closed" is the expectation of `g` under the
pinned-closed law. -/
theorem integral_comp_sdiff_singleton (π : Sym2 V → unitInterval) (e : Sym2 V)
    {g : Config V → ℝ} (hg : Measurable g) :
    ∫ ω, g (ω \ {e}) ∂(PercLib.Percolation.Bond.law π)
      = ∫ ω, g ω ∂(PercLib.Percolation.Bond.law (Function.update π e 0)) := by
  rw [← map_sdiff_singleton_law π e,
    MeasureTheory.integral_map (PercLib.Probability.measurable_diff_singleton e).aemeasurable
      hg.aestronglyMeasurable]

/-! ## 2. The single-coordinate factorization at a closed coordinate, for `L¹` `G` -/

/-- The positive/negative-part identity `max a 0 - max (-a) 0 = a`. -/
theorem max_zero_sub_max_neg_zero (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

/-- **Closed-coordinate factorization for an integrable observation.**

If `G` is measurable, integrable for the Bernoulli law and depends only on the coordinates
other than `e`, then averaging it against the indicator of the closed event `e ∉ ω` costs
exactly the factor `1 - π e`.

This is the `L¹` form of the landed `integral_compl_indicator_mul_of_sdiff_determined`, whose
nonnegativity hypothesis was used only to be able to invoke the `ℝ≥0∞` factorisation; the
positive and negative parts of `G` are handled separately here and the two halves are
reassembled with `integral_sub`.  Neither boundedness nor domination is used. -/
theorem integral_compl_indicator_mul_of_sdiff_determined_of_integrable
    (π : Sym2 V → unitInterval) (e : Sym2 V) {G : Config V → ℝ}
    (hG : Measurable G) (hdet : ∀ ω : Config V, G ω = G (ω \ {e}))
    (hint : Integrable G (PercLib.Percolation.Bond.law π)) :
    ∫ ω, (if e ∈ ω then 0 else G ω) ∂(PercLib.Percolation.Bond.law π)
      = (1 - (π e : ℝ)) * ∫ ω, G ω ∂(PercLib.Percolation.Bond.law π) := by
  classical
  set μ := PercLib.Percolation.Bond.law π with hμ
  let Gp : Config V → ℝ := fun ω => max (G ω) 0
  let Gm : Config V → ℝ := fun ω => max (-(G ω)) 0
  have hGpmax : ∀ ω, Gp ω = max (G ω) 0 := fun _ => rfl
  have hGmmax : ∀ ω, Gm ω = max (-(G ω)) 0 := fun _ => rfl
  have hGpM : Measurable Gp := by
    dsimp only [Gp]
    exact hG.max measurable_const
  have hGmM : Measurable Gm := by
    dsimp only [Gm]
    exact hG.neg.max measurable_const
  have hGp0 : ∀ ω : Config V, 0 ≤ Gp ω := fun ω => by rw [hGpmax]; exact le_max_right _ _
  have hGm0 : ∀ ω : Config V, 0 ≤ Gm ω := fun ω => by rw [hGmmax]; exact le_max_right _ _
  have hGpdet : ∀ ω : Config V, Gp ω = Gp (ω \ {e}) := by
    intro ω; rw [hGpmax, hGpmax, hdet ω]
  have hGmdet : ∀ ω : Config V, Gm ω = Gm (ω \ {e}) := by
    intro ω; rw [hGmmax, hGmmax, hdet ω]
  have hbound : ∀ ω : Config V, ‖(if e ∈ ω then (0 : ℝ) else Gp ω)‖ ≤ |G ω| := by
    intro ω
    by_cases h : e ∈ ω
    · rw [ite_eq_left h, norm_zero]; exact abs_nonneg _
    · rw [ite_eq_right h, Real.norm_eq_abs, abs_of_nonneg (hGp0 ω), hGpmax ω]
      exact max_le (le_abs_self _) (abs_nonneg _)
  have hboundm : ∀ ω : Config V, ‖(if e ∈ ω then (0 : ℝ) else Gm ω)‖ ≤ |G ω| := by
    intro ω
    by_cases h : e ∈ ω
    · rw [ite_eq_left h, norm_zero]; exact abs_nonneg _
    · rw [ite_eq_right h, Real.norm_eq_abs, abs_of_nonneg (hGm0 ω), hGmmax ω]
      have hle : max (-(G ω)) 0 ≤ |-(G ω)| := max_le (le_abs_self _) (abs_nonneg _)
      simpa only [abs_neg] using hle
  have hIkp : Integrable (fun ω : Config V => if e ∈ ω then (0 : ℝ) else Gp ω) μ :=
    hint.abs.mono' (Measurable.ite (measurableSet_mem e) measurable_const hGpM).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hIkm : Integrable (fun ω : Config V => if e ∈ ω then (0 : ℝ) else Gm ω) μ :=
    hint.abs.mono' (Measurable.ite (measurableSet_mem e) measurable_const hGmM).aestronglyMeasurable
      (Filter.Eventually.of_forall hboundm)
  have hIp : Integrable Gp μ := by
    refine Integrable.mono' hint.abs hGpM.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hGp0 ω), hGpmax ω]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hIm : Integrable Gm μ := by
    refine Integrable.mono' hint.abs hGmM.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hGm0 ω), hGmmax ω]
    have hle : max (-(G ω)) 0 ≤ |-(G ω)| := max_le (le_abs_self _) (abs_nonneg _)
    simpa only [abs_neg] using hle
  have hAp := integral_compl_indicator_mul_of_sdiff_determined π e hGpM hGpdet hGp0
  have hAm := integral_compl_indicator_mul_of_sdiff_determined π e hGmM hGmdet hGm0
  have hsplit : (fun ω : Config V => if e ∈ ω then (0 : ℝ) else G ω)
      = fun ω => (if e ∈ ω then (0 : ℝ) else Gp ω)
          - (if e ∈ ω then (0 : ℝ) else Gm ω) := by
    funext ω
    by_cases h : e ∈ ω
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]; ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, hGpmax ω, hGmmax ω,
        max_zero_sub_max_neg_zero]
  rw [hsplit, integral_sub hIkp hIkm, hAp, hAm]
  have hsub : (∫ ω, G ω ∂μ) = (∫ ω, Gp ω ∂μ) - ∫ ω, Gm ω ∂μ := by
    rw [← integral_sub hIp hIm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change G ω = Gp ω - Gm ω
    rw [hGpmax ω, hGmmax ω, max_zero_sub_max_neg_zero]
  rw [hsub]
  ring

/-! ## 3. The pivotal flux as a difference of pinned expectations -/

/-- **The flip mean is the difference of the two pinned expectations.**

`flipDiff g e ω = g (ω ∪ {e}) - g (ω \ {e})` is the difference of the two single-coordinate
modifications of `g`, so its mean is the difference of the means of `g` under the two pinned
laws.  Integrability at the two pinned laws is exactly what makes the two means finite and the
subtraction legitimate; no boundedness is used. -/
theorem pivotalFlux_eq_integral_pinned (π : Sym2 V → unitInterval) (e : Sym2 V)
    {g : Config V → ℝ} (hg : Measurable g)
    (h₁ : Integrable g (PercLib.Percolation.Bond.law (Function.update π e 1)))
    (h₀ : Integrable g (PercLib.Percolation.Bond.law (Function.update π e 0))) :
    pivotalFlux (PercLib.Percolation.Bond.law π) g e
      = (∫ ω, g ω ∂(PercLib.Percolation.Bond.law (Function.update π e 1)))
        - ∫ ω, g ω ∂(PercLib.Percolation.Bond.law (Function.update π e 0)) := by
  classical
  set μ := PercLib.Percolation.Bond.law π with hμ
  have hIP : Integrable (fun ω : Config V => g (ω ∪ {e})) μ := by
    have hg' : Integrable g (Measure.map (fun ω : Config V => ω ∪ {e}) μ) := by
      rw [hμ, map_union_singleton_law π e]; exact h₁
    have h := (MeasureTheory.integrable_map_measure (μ := μ)
      (f := fun ω : Config V => ω ∪ {e}) (g := g) hg.aestronglyMeasurable
      (measurable_union_singleton e).aemeasurable).mp hg'
    simpa [Function.comp_def] using h
  have hIQ : Integrable (fun ω : Config V => g (ω \ {e})) μ := by
    have hg' : Integrable g (Measure.map (fun ω : Config V => ω \ {e}) μ) := by
      rw [hμ, map_sdiff_singleton_law π e]; exact h₀
    have h := (MeasureTheory.integrable_map_measure (μ := μ)
      (f := fun ω : Config V => ω \ {e}) (g := g) hg.aestronglyMeasurable
      (PercLib.Probability.measurable_diff_singleton e).aemeasurable).mp hg'
    simpa [Function.comp_def] using h
  unfold pivotalFlux
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)]
  · rw [integral_sub hIP hIQ, integral_comp_union_singleton π e hg,
      integral_comp_sdiff_singleton π e hg]
  · rw [flipDiff, forceOn_singleton_open_eq, forceOn_singleton_closed_eq]

/-! ## 4. The closed-event factorization for `L¹` observations -/

/-- **The `(1 - q_e)` factor is absorbed by the closed-edge event, for an `L¹` observation.**

This is `one_sub_mul_pivotalFlux_eq` without the boundedness hypothesis: the only input is
integrability of `g` at the two single-coordinate pinned laws.  The degenerate values
`π e = 0` and `π e = 1` need no separate treatment: the identity is a single algebraic
computation in which the pinned laws absorb the degeneracy. -/
theorem one_sub_mul_pivotalFlux_eq_of_integrable (π : Sym2 V → unitInterval) (e : Sym2 V)
    {g : Config V → ℝ} (hg : Measurable g)
    (h₁ : Integrable g (PercLib.Percolation.Bond.law (Function.update π e 1)))
    (h₀ : Integrable g (PercLib.Percolation.Bond.law (Function.update π e 0))) :
    (1 - (π e : ℝ)) * pivotalFlux (PercLib.Percolation.Bond.law π) g e
      = ∫ ω, (if e ∈ ω then 0 else (g (ω ∪ {e}) - g ω))
          ∂(PercLib.Percolation.Bond.law π) := by
  classical
  set μ := PercLib.Percolation.Bond.law π with hμ
  obtain ⟨P, hP⟩ : ∃ P : Config V → ℝ, ∀ ω, P ω = g (ω ∪ {e}) := ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Config V → ℝ, ∀ ω, Q ω = g (ω \ {e}) := ⟨_, fun _ => rfl⟩
  have hMP : Measurable P := by
    rw [show P = (fun ω => g (ω ∪ {e})) from funext fun ω => (hP ω)]
    exact hg.comp (measurable_union_singleton e)
  have hMQ : Measurable Q := by
    rw [show Q = (fun ω => g (ω \ {e})) from funext fun ω => hQ ω]
    exact hg.comp (PercLib.Probability.measurable_diff_singleton e)
  have hIP : Integrable P μ := by
    have hg' : Integrable g (Measure.map (fun ω : Config V => ω ∪ {e}) μ) := by
      rw [hμ, map_union_singleton_law π e]; exact h₁
    have h := (MeasureTheory.integrable_map_measure (μ := μ)
      (f := fun ω : Config V => ω ∪ {e}) (g := g) hg.aestronglyMeasurable
      (measurable_union_singleton e).aemeasurable).mp hg'
    exact h.congr (Filter.Eventually.of_forall fun ω => (hP ω).symm)
  have hIQ : Integrable Q μ := by
    have hg' : Integrable g (Measure.map (fun ω : Config V => ω \ {e}) μ) := by
      rw [hμ, map_sdiff_singleton_law π e]; exact h₀
    have h := (MeasureTheory.integrable_map_measure (μ := μ)
      (f := fun ω : Config V => ω \ {e}) (g := g) hg.aestronglyMeasurable
      (PercLib.Probability.measurable_diff_singleton e).aemeasurable).mp hg'
    exact h.congr (Filter.Eventually.of_forall fun ω => (hQ ω).symm)
  have hPdet : ∀ ω : Config V, P ω = P (ω \ {e}) := by
    intro ω; rw [hP, hP, sdiff_singleton_union]
  have hQdet : ∀ ω : Config V, Q ω = Q (ω \ {e}) := by
    intro ω; rw [hQ, hQ, sdiff_singleton_idem]
  have hIkP : Integrable (fun ω : Config V => if e ∈ ω then (0 : ℝ) else P ω) μ := by
    refine hIP.abs.mono' (Measurable.ite (measurableSet_mem e) measurable_const hMP).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    by_cases h : e ∈ ω
    · rw [ite_eq_left h, norm_zero]; exact abs_nonneg _
    · rw [ite_eq_right h]
      rw [Real.norm_eq_abs]
  have hIkQ : Integrable (fun ω : Config V => if e ∈ ω then (0 : ℝ) else Q ω) μ := by
    refine hIQ.abs.mono' (Measurable.ite (measurableSet_mem e) measurable_const hMQ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    by_cases h : e ∈ ω
    · rw [ite_eq_left h, norm_zero]; exact abs_nonneg _
    · rw [ite_eq_right h]
      rw [Real.norm_eq_abs]
  have hAP := integral_compl_indicator_mul_of_sdiff_determined_of_integrable π e hMP hPdet hIP
  have hAQ := integral_compl_indicator_mul_of_sdiff_determined_of_integrable π e hMQ hQdet hIQ
  have hpf := pivotalFlux_eq_integral_pinned π e hg h₁ h₀
  have hPeq : (∫ ω, P ω ∂μ)
      = ∫ ω, g ω ∂(PercLib.Percolation.Bond.law (Function.update π e 1)) := by
    rw [hμ]
    simpa only [hP] using integral_comp_union_singleton π e hg
  have hQeq : (∫ ω, Q ω ∂μ)
      = ∫ ω, g ω ∂(PercLib.Percolation.Bond.law (Function.update π e 0)) := by
    rw [hμ]
    simpa only [hQ] using integral_comp_sdiff_singleton π e hg
  rw [hpf]
  have hfinal : (fun ω : Config V => if e ∈ ω then (0 : ℝ) else (g (ω ∪ {e}) - g ω))
      = fun ω => (if e ∈ ω then (0 : ℝ) else P ω) - (if e ∈ ω then (0 : ℝ) else Q ω) := by
    funext ω
    by_cases h : e ∈ ω
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]; ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, hP ω, hQ ω,
        sdiff_singleton_of_notMem h]
  rw [hfinal, integral_sub hIkP hIkQ, hAP, hAQ, hPeq, hQeq]
  ring

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration

#print axioms map_union_singleton_law
#print axioms map_sdiff_singleton_law
#print axioms integral_comp_union_singleton
#print axioms integral_comp_sdiff_singleton
#print axioms max_zero_sub_max_neg_zero
#print axioms integral_compl_indicator_mul_of_sdiff_determined_of_integrable
#print axioms pivotalFlux_eq_integral_pinned
#print axioms one_sub_mul_pivotalFlux_eq_of_integrable

end PercLib.CriticalLRP.Orchestration
