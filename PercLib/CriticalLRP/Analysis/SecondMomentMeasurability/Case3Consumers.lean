/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Case 3 of Proposition I.4.15 with the measurability hypotheses removed

Swarm `smwyvlg99`, member `m2`, direction `d2`.

`SecondMomentCase3.regularlyVarying_two_of_case3` carries `hmR : Measurable M.rhsScalarTwo`, and
`SecondMomentCase3.tendsto_div_two_of_case3` carries `hmeasE2 : Measurable M.p2ExclError` and
`hmeasEbar : Measurable M.p2Ebar`.  Both are restated here with those hypotheses deleted and
**nothing added**: the measurabilities follow from the tail finiteness `h1`, `h2` that both
statements already assume (`SourceModelData.measurable_rhsScalarTwo_of_tail`,
`measurable_p2ExclError_of_tail`, `measurable_p2Ebar_of_tail` in `Consumers.lean`).

The radial-regularity inputs `hac`, `hae` and the Case-3 numerator/gap inputs are the shipped ones,
unchanged.

No `sorry`, `admit`, `native_decide` or custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Consumers
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3

/-! # Removing Case-3 measurability premises -/

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

namespace SecondMomentCase3

variable (M : SourceModelData)

/-- `regularlyVarying_two_of_case3` with `hmR` discharged from `h2`. -/
theorem regularlyVarying_two_of_case3_no_hmR (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {K c c3 : ℝ} (hK : 0 ≤ K) (hc3 : 0 < c3)
    (hcn : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0)) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two_of_case3 hα hr₀ hβ hac (M.measurable_rhsScalarTwo_of_tail h2) hae h1 h2
    hP hK hc3 hcn hnum hgm hdrv

/-- `tendsto_div_two_of_case3` with `hmeasE2`, `hmeasEbar` discharged from `h1`, `h2`. -/
theorem tendsto_div_two_of_case3_no_meas (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {K c c3 : ℝ} (hK : 0 ≤ K) (hc3 : 0 < c3)
    (hcn : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hnum : ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      K * ((M.ball r).ncard : ℝ) * M.case3Driver c r * (M.cutMassAt r 0).toReal ^ 4)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0))
    (hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c))
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M)) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  M.tendsto_div_two_of_case3 hα hr₀ hβ hac hae h1 h2 hP hK hc3 hcn hnum hgm hdrv hlogdrv
    (M.measurable_p2ExclError_of_tail h1 h2) (M.measurable_p2Ebar_of_tail hα h1 h2) hlogH hlogE0

end SecondMomentCase3

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.SecondMomentCase3.regularlyVarying_two_of_case3_no_hmR
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.SecondMomentCase3.tendsto_div_two_of_case3_no_meas
