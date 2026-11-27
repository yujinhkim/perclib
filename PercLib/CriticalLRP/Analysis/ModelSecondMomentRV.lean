/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwyrvajs`, member `m1`,
direction (A), at production base `f6643492ceecda8b5282ee0d6f3eebafb44ee6f5`.

# Proposition I.4.15 at the actual cutoff second moment, modulo explicit model data

Instantiation of `PercLib.CriticalLRP.SecondMomentRV.secondMoment_regularlyVarying` at the real
second cutoff moment `r ↦ E_{b_c,r}|K|^2` of Definition I.1.5, in the `momOf` spelling used by
the higher-moment packet of `VolumeMoments/HigherMoments`.

The paper's display (I.4.15) is

  `d/dr E_{b_c,r}|K|^2 = 3α (1 - Ebar_{2,r}) r⁻¹ E_{b_c,r}|K|^2`,

with `Ebar_{2,r}` the error of (I.4.14)-(I.4.16).  The theorems below consume exactly that
identity, in the corner-safe form an off-corner/a.e. derivation can supply:

* `hac`  : absolute continuity of `r ↦ E_{b_c,r}|K|^2` on every window `[r₀,R]` of the tail;
* `hae`  : `HasDerivAt (r ↦ E_{b_c,r}|K|^2) (3α (1 - E t) (E_{b_c,t}|K|^2)/t) t` a.e. on `[r₀,∞)`;
* `hmE`, `hE0` : `E` measurable and `E → 0`;
* `hlog` : logarithmic integrability of `E` (only for the `~ A r^{3α}` refinement).

**These model-side premises are not proved here.**  In particular no error function `E` is
constructed, and Proposition I.4.15 is not claimed: what is proved is that the analytic part of
the proposition — the passage from the linear ODE (I.4.15) to regular variation and, under
logarithmic integrability, to `~ A r^{3α}` — is complete at the actual model object, with the
remaining obligations named.
-/
module

public import PercLib.CriticalLRP.Analysis.MomentRegularVariation
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Defs
public import PercLib.CriticalLRP.Analysis.SecondMomentRV

/-! # Conditional regular variation of the actual cutoff second moment -/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

open PercLib.CriticalLRP.Analysis
open PercLib.CriticalLRP.SecondMomentRV
open PercLib.CriticalLRP.I420Case3 (momOf)

variable (M : SourceModelData)

/-- **Case 1/2 of Proposition I.4.15, analytic part, at the actual second cutoff moment.**

Assume the first-moment asymptotic `hP` (so that every cutoff moment is positive), the
corner-safe radial regularity of `r ↦ E_{b_c,r}|K|^2` (absolute continuity on compact windows
plus the a.e. identity (I.4.15) with error `E`), `E` measurable and `E → 0`.  Then
`r ↦ E_{b_c,r}|K|^2` is regularly varying of index `3α`.

`hac` and `hae` are exactly the model obligations that an off-corner/a.e. second-moment radial
identity has to produce; they are not derived here. -/
theorem momOf_two_regularlyVarying_of_ae_linear_ode (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) r₀ R)
    {E : ℝ → ℝ} (hmE : Measurable E) (hE0 : Tendsto E atTop (𝓝 0))
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
        (3 * M.α * (1 - E t) * momOf (fun r => M.cutProb r) (0 : M.V) 2 t / t) t) :
    RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
      (3 * M.α) := by
  refine secondMoment_regularlyVarying (f := fun r : ℝ =>
    momOf (fun r => M.cutProb r) (0 : M.V) 2 r) hα hr₀ hac ?_ hae hmE hE0
  intro t ht
  exact M.momOf_pos_of_hP (c := M.α / (M.betaCrit : ℝ)) hP 2 t (lt_of_lt_of_le hr₀ ht)

/-- **The `d > 3α` refinement of Proposition I.4.15, analytic part**, at the actual second
cutoff moment: under the hypotheses of `momOf_two_regularlyVarying_of_ae_linear_ode` and
logarithmic integrability of the error, `E_{b_c,r}|K|^2 / r^{3α}` converges to a positive
limit. -/
theorem momOf_two_tendsto_div_of_ae_linear_ode (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) r₀ R)
    {E : ℝ → ℝ} (hmE : Measurable E) (hE0 : Tendsto E atTop (𝓝 0))
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
        (3 * M.α * (1 - E t) * momOf (fun r => M.cutProb r) (0 : M.V) 2 t / t) t)
    (hlog : LogarithmicallyIntegrable E) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r / r ^ (3 * M.α))
      atTop (𝓝 A) := by
  refine secondMoment_tendsto_div (f := fun r : ℝ =>
    momOf (fun r => M.cutProb r) (0 : M.V) 2 r) hα hr₀ hac ?_ hae hmE hE0 hlog
  intro t ht
  exact M.momOf_pos_of_hP (c := M.α / (M.betaCrit : ℝ)) hP 2 t (lt_of_lt_of_le hr₀ ht)

/-- The `~ A r^{3α}` form of `momOf_two_tendsto_div_of_ae_linear_ode`. -/
theorem momOf_two_tendsto_div_normalized_of_ae_linear_ode (hα : 0 < M.α) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) r₀ R)
    {E : ℝ → ℝ} (hmE : Measurable E) (hE0 : Tendsto E atTop (𝓝 0))
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
        (3 * M.α * (1 - E t) * momOf (fun r => M.cutProb r) (0 : M.V) 2 t / t) t)
    (hlog : LogarithmicallyIntegrable E) :
    ∃ c : ℝ, 0 < c ∧ Tendsto
      (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r / (c * r ^ (3 * M.α)))
      atTop (𝓝 1) := by
  refine secondMoment_tendsto_div_normalized (f := fun r : ℝ =>
    momOf (fun r => M.cutProb r) (0 : M.V) 2 r) hα hr₀ hac ?_ hae hmE hE0 hlog
  intro t ht
  exact M.momOf_pos_of_hP (c := M.α / (M.betaCrit : ℝ)) hP 2 t (lt_of_lt_of_le hr₀ ht)

/-- **Proposition I.4.15 Case 1/2, analytic part, from the source `p = 2` right-hand side.**

This is the same conclusion as `momOf_two_regularlyVarying_of_ae_linear_ode`, but with the
derivative value left in the source's own `p = 2` vocabulary `M.rhsScalarTwo` (the real
`β_c(-K'(r))` times the excluded masses, `Analysis/Cutoff/SecondMoment/Defs.lean`).  The error
function and its measurability are then *derived*, and the only asymptotic input is

  `t · M.rhsScalarTwo t / (3α E_{b_c,t}|K|^2) → 1`,

which is precisely `Ebar_{2,t} → 0` of (I.4.14)-(I.4.16) rewritten as `f' ~ 3α f / t`.

Remaining model obligations, named: the a.e. radial identity at `p = 2` in `rhsScalarTwo`
form, measurability of the two factors, and the ratio limit. -/
theorem momOf_two_regularlyVarying_of_rhsScalarTwo (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) r₀ R)
    (hmf : Measurable (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r))
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
        (M.rhsScalarTwo t) t)
    (hratio : Tendsto (fun t : ℝ => t * M.rhsScalarTwo t
      / (3 * M.α * momOf (fun r => M.cutProb r) (0 : M.V) 2 t)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
      (3 * M.α) :=
  secondMoment_regularlyVarying_of_rhs (f := fun r : ℝ =>
    momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (rhs := M.rhsScalarTwo) hα hr₀ hac
    (fun t ht => M.momOf_pos_of_hP (c := M.α / (M.betaCrit : ℝ)) hP 2 t
      (lt_of_lt_of_le hr₀ ht)) hmf hmR hae hratio

/-- **The whole higher-moment side-premise packet, with the second-moment regular variation
*derived* rather than assumed.**

`Analysis.MomentRegularVariation.SourceModelData.momOf_packet` takes the second-moment regular
variation as an independent input (`h2`, "the one genuinely independent input, matching
Proposition I.4.15 / gap WS002").  Composing it with
`momOf_two_regularlyVarying_of_ae_linear_ode` removes that input: positivity, measurability of
both moments, the first-moment regular variation and the second-moment regular variation all
follow from `hP` together with the explicit model data `hac`, `hae`, `hmE`, `hE0`. -/
theorem momOf_packet_of_ae_linear_ode (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) r₀ R)
    {E : ℝ → ℝ} (hmE : Measurable E) (hE0 : Tendsto E atTop (𝓝 0))
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
        (3 * M.α * (1 - E t) * momOf (fun r => M.cutProb r) (0 : M.V) 2 t / t) t) :
    (∀ m : ℕ, ∀ r : ℝ, 0 < r → 0 < momOf (fun r => M.cutProb r) (0 : M.V) m r) ∧
      Measurable (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) ∧
      Measurable (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) ∧
      RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α ∧
      RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
        (3 * M.α) :=
  M.momOf_packet hα hβ hP
    (M.momOf_two_regularlyVarying_of_ae_linear_ode hα hr₀ hβ hP hac hmE hE0 hae)

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_two_regularlyVarying_of_ae_linear_ode
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_two_tendsto_div_of_ae_linear_ode
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_two_tendsto_div_normalized_of_ae_linear_ode
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_two_regularlyVarying_of_rhsScalarTwo
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_packet_of_ae_linear_ode

end SourceModelData

end PercLib.CriticalLRP.Orchestration
