/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The measurability inputs of the second-moment chain, removed from the shipped statements

Swarm `smwyvlg99`, member `m2`, direction `d2`.

`Main.lean` proves `Measurable M.rhsScalarTwo` and `Errors.lean` proves
`Measurable M.p2ExclError`, `Measurable M.p2H` and `Measurable M.p2Ebar` from

`h4 : ∀ x > 0, ∃ r₁ > x, M.cutMoment 4 r₁ ≠ ⊤`.

This file removes the measurability hypotheses from the shipped statements.  The key point is that
`h4` itself is **not a new hypothesis**: `CaseOne.cutMoment_four_ne_top_of_two` turns finiteness of
the *second* cutoff moment at a radius into finiteness of the fourth, and the shipped statements
already carry the tail finiteness `h2 : ∀ t ≥ r₀, M.cutMoment 2 t ≠ ⊤`.  Hence

* `Measurable M.rhsScalarTwo`,
* `Measurable M.p2ExclError`,
* `Measurable M.p2Ebar`

follow from `h1`, `h2` alone, and the statements

`regularlyVarying_two`, `regularlyVarying_two_of_hP_of_ae_deriv`, `regularlyVarying_two_reduced`,
`momOf_two_regularlyVarying`, `CaseOne.tendsto_div_two_of_caseOne`,
`CaseOne.regularlyVarying_two_of_caseOne`

are restated below with `hmR`/`hmeasE2`/`hmeasEbar` **deleted and nothing added**: every remaining
hypothesis (`hac`, `hae`, `hmf`, `h1`, `h2`, `hP`, `hE2`, `hH`, `hE0`, `hc`, `hratio`, `h3α`, `hκ`,
`hHlog`, `hE0log`) is the shipped one, passed through unchanged.

The radial-regularity inputs `hac` (interval absolute continuity) and `hae` (the a.e. radial
identity) are untouched: they are direction (A) of the swarm, not discharged here.

No `sorry`, `admit`, `native_decide` or custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Errors
public import PercLib.CriticalLRP.Analysis.SecondMomentCase1

/-! # Removing radial measurability premises -/

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

/-! ## 0. Global finiteness and the fourth moment from the second -/

/-- Tail finiteness of a cutoff moment gives global finiteness, by monotonicity. -/
theorem cutMoment_ne_top_of_tail {p : ℕ} {r₀ : ℝ}
    (h : ∀ t : ℝ, r₀ ≤ t → M.cutMoment p t ≠ ⊤) :
    ∀ t : ℝ, M.cutMoment p t ≠ ⊤ := by
  intro t
  rcases le_total t r₀ with ht | ht
  · exact ne_top_of_le_ne_top (h r₀ le_rfl) (M.cutMoment_monotone p ht)
  · exact h t ht

/-- **The fourth-moment tail finiteness used by `Main`/`Errors` is the chain's own `h2`.**

At every positive radius, the radius `x + 1` is strictly larger and its fourth cutoff moment is
finite as soon as the second one is (`CaseOne.cutMoment_four_ne_top_of_two`). -/
theorem fourthMoment_tail_of_two (h2 : ∀ r : ℝ, M.cutMoment 2 r ≠ ⊤) :
    ∀ x : ℝ, 0 < x → ∃ r1 : ℝ, x < r1 ∧ M.cutMoment 4 r1 ≠ ⊤ :=
  fun x _ => ⟨x + 1, by linarith, CaseOne.cutMoment_four_ne_top_of_two M (h2 (x + 1))⟩

/-! ## 1. The three measurability inputs, from `h1` and `h2` only -/

/-- `Measurable M.rhsScalarTwo` from tail finiteness of the second cutoff moment. -/
theorem measurable_rhsScalarTwo_of_tail {r₀ : ℝ}
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    Measurable M.rhsScalarTwo :=
  M.measurable_rhsScalarTwo (M.fourthMoment_tail_of_two (M.cutMoment_ne_top_of_tail h2))

/-- `Measurable M.p2ExclError` from tail finiteness of the first and second cutoff moments. -/
theorem measurable_p2ExclError_of_tail {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    Measurable M.p2ExclError :=
  M.measurable_p2ExclError (M.cutMoment_ne_top_of_tail h1) (M.cutMoment_ne_top_of_tail h2)
    (M.fourthMoment_tail_of_two (M.cutMoment_ne_top_of_tail h2))

/-- `Measurable M.p2Ebar` from tail finiteness of the first and second cutoff moments. -/
theorem measurable_p2Ebar_of_tail (hα : 0 < M.α) {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    Measurable M.p2Ebar :=
  M.measurable_p2Ebar hα (M.cutMoment_ne_top_of_tail h1) (M.cutMoment_ne_top_of_tail h2)
    (M.fourthMoment_tail_of_two (M.cutMoment_ne_top_of_tail h2))

/-- **The `hmeas` input of `Integrated/LocalFTC.lean` and `WindowMajorant/Main.lean`** (a.e. strong
measurability of the derivative weight on a radius interval) follows from the same tail finiteness,
so those files no longer need the fixed-radius flux convergence to supply it. -/
theorem aestronglyMeasurable_rhsScalarTwo_restrict {r₀ : ℝ}
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) (a b : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => M.rhsScalarTwo t) (volume.restrict (Set.uIoc a b)) :=
  (M.measurable_rhsScalarTwo_of_tail h2).aestronglyMeasurable

/-! ## 2. `regularlyVarying_two` without `hmR` -/

theorem regularlyVarying_two_no_hmR
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmf : Measurable (fun r : ℝ => (M.cutMoment 2 r).toReal))
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two hα hr₀ hβ hac hmf (M.measurable_rhsScalarTwo_of_tail h2) hae h1 h2
    hE2 hH hE0

/-! ## 3. `regularlyVarying_two_of_hP_of_ae_deriv` without `hmR` -/

theorem regularlyVarying_two_of_hP_of_ae_deriv_no_hmR
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two_of_hP_of_ae_deriv hα hr₀ hβ hac (M.measurable_rhsScalarTwo_of_tail h2) hae
    h1 h2 hP hE2

/-! ## 4. The headline reduced form `regularlyVarying_two_reduced` without `hmR` -/

theorem regularlyVarying_two_reduced_no_hmR
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hc : ∀ᶠ r : ℝ in atTop, M.connCubeMass r ≠ ⊤)
    (hratio : Tendsto (fun r : ℝ => (M.connCubeMass r).toReal
        / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal))
      atTop (𝓝 0)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two_reduced hα hr₀ hβ hac (M.measurable_rhsScalarTwo_of_tail h2) hae h1 h2 hP
    hc hratio

/-! ## 5. `momOf_two_regularlyVarying` without `hmR` -/

theorem momOf_two_regularlyVarying_no_hmR
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmf : Measurable (fun r : ℝ => (M.cutMoment 2 r).toReal))
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hE2 : Tendsto M.p2ExclError atTop (𝓝 0))
    (hH : Tendsto M.p2H atTop (𝓝 0))
    (hE0 : Tendsto (PivotFlux.cutE0 M) atTop (𝓝 0)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => I420Case3.momOf (fun r => M.cutProb r) 0 2 r)
      (3 * M.α) :=
  M.momOf_two_regularlyVarying hα hr₀ hβ hac hmf (M.measurable_rhsScalarTwo_of_tail h2) hae h1 h2
    hE2 hH hE0

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 6. Case 1 of Proposition I.4.15 with the three measurability hypotheses removed -/

namespace PercLib.CriticalLRP.CaseOne

open PercLib.CriticalLRP.Orchestration
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

/-- `tendsto_div_two_of_caseOne` with `hmeasE2` and `hmeasEbar` discharged, nothing added. -/
theorem tendsto_div_two_of_caseOne_no_meas (M : SourceModelData)
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hHlog : Analysis.LogarithmicallyIntegrable M.p2H)
    (hE0log : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M)) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  tendsto_div_two_of_caseOne M hα hr₀ hβ h3α hκ hac hae h1 h2 hP hHlog hE0log
    (M.measurable_p2ExclError_of_tail h1 h2) (M.measurable_p2Ebar_of_tail hα h1 h2)

/-- `regularlyVarying_two_of_caseOne` with `hmR` discharged, nothing added. -/
theorem regularlyVarying_two_of_caseOne_no_hmR (M : SourceModelData)
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h3α : 3 * M.α < (M.d : ℝ))
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  regularlyVarying_two_of_caseOne M hα hr₀ hβ h3α hκ hac (M.measurable_rhsScalarTwo_of_tail h2)
    hae h1 h2 hP

end PercLib.CriticalLRP.CaseOne

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_rhsScalarTwo_of_tail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_p2ExclError_of_tail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_p2Ebar_of_tail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.aestronglyMeasurable_rhsScalarTwo_restrict
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_reduced_no_hmR
#print axioms PercLib.CriticalLRP.CaseOne.tendsto_div_two_of_caseOne_no_meas
#print axioms PercLib.CriticalLRP.CaseOne.regularlyVarying_two_of_caseOne_no_hmR
