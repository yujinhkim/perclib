/-
Ultramath swarm `smwzlje3f`, member `m5`, direction `d5`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m5/Main.lean`.

# Proposition I.4.15, Case 3, with the cited volume tail in place of the moment gap

`ProductGap/SourceConsumer.lean` proves the Case-3 conclusions from the explicit moment gap

`{c₃} (hc₃ : 0 < c₃) (hgm : ∀ᶠ r in atTop, c₃ * (E_{β_c,r}|K|)³ ≤ E_{β_c,r}|K|²)`

whose only justification in the source is the display quoted in `Defs.lean`: the triangle
condition implies `P_{β_c}(|K| ≥ n) ⪯ n^{-1/2}` (cited), which the source optimizes against
`E_{β_c,r}|K| ≤ N^{1/2} + N^{-1} E_{β_c,r}|K|²`.

Here `hgm` is *derived*, not assumed.  Every theorem below has exactly the hypotheses of its
`..._of_source_p21` counterpart in `ProductGap/SourceConsumer.lean` except that

  `{c₃ : ℝ} (hc₃ : 0 < c₃) (hgm : ∀ᶠ r in atTop, c₃ * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)`

is replaced by the single source-cited input

  `{C : ℝ} (hC : 0 ≤ C) (hVolTail : M.CriticalVolumeTail C)`,

and the constant is no longer free: the gap holds with `c₃ = (4C+1)^{-3}` (see
`momentGap_of_volumeTail`).  This is a *strengthening* of the interface in the direction of source
fidelity, not a weakening: the numeric gap `hgm` is not derivable from `h1`, `h2` or the triangle
condition inside production, while `hVolTail` is exactly what the source cites.

The matching technical gain is that `I420Case3.case3_hgm_of_tail` and
`exists_momentGap_of_volumeTail` require `M.cutMoment 2 t ≠ ⊤` for *every* `t ≥ 1`, whereas the
Case-3 interface only provides finiteness for `t ≥ r₀` with `r₀ > 0` arbitrary.  The version
below only needs finiteness on `{t | max 1 r₀ ≤ t}`, which is the form actually supplied.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- The moment gap in the `∀ᶠ` form used by the Case-3 consumers, derived from the cited uncut
volume tail.  Only finiteness of the cutoff second moment on `{t | max 1 r₀ ≤ t}` is needed,
which is weaker than the `∀ t ≥ 1` form required by `exists_momentGap_of_volumeTail`. -/
theorem exists_momentGap_of_volumeTail_soon {C : ℝ} (hC : 0 ≤ C) {r₀ : ℝ}
    (hVolTail : M.CriticalVolumeTail C)
    (h2 : ∀ t : ℝ, max 1 r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal := by
  refine ⟨(Analysis.Route3.ratioConst C)⁻¹,
    inv_pos.mpr (Analysis.Route3.ratioConst_pos hC), ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 r₀)] with r hr
  exact M.momentGap_of_volumeTail hC hVolTail
    (lt_of_lt_of_le one_pos (le_trans (le_max_left 1 r₀) hr)) (h2 r hr)

/-- `𝓔_{2,r} → 0` in Case 3, from the cited uncut volume tail instead of `hgm`. -/
theorem p2ExclError_tendsto_zero_of_source_volumeTail {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {C : ℝ} (hC : 0 ≤ C) (hVolTail : M.CriticalVolumeTail C) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  obtain ⟨c, Cp, -, -, hCp0, hdrv, -, hW3, hP4⟩ :=
    M.exists_repaired_case3_polygon_bundle hC₀ hp hP hTri hF
  obtain ⟨c3, hc3, hgm⟩ := M.exists_momentGap_of_volumeTail_soon hC hVolTail
    (fun t ht => h2 t (le_trans (le_max_right 1 r₀) ht))
  exact M.p2ExclError_tendsto_zero_of_polygonBundle hCp0 hW3 hP4 hdrv h1 h2 hc3 hgm

/-- Logarithmic integrability of `𝓔_{2,r}` in Case 3, from the cited uncut volume tail. -/
theorem logIntegrable_p2ExclError_of_source_volumeTail {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hmeas : Measurable M.p2ExclError)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {C : ℝ} (hC : 0 ≤ C) (hVolTail : M.CriticalVolumeTail C) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  obtain ⟨c, Cp, -, -, hCp0, -, hlogdrv, hW3, hP4⟩ :=
    M.exists_repaired_case3_polygon_bundle hC₀ hp hP hTri hF
  obtain ⟨c3, hc3, hgm⟩ := M.exists_momentGap_of_volumeTail_soon hC hVolTail
    (fun t ht => h2 t (le_trans (le_max_right 1 r₀) ht))
  exact M.logIntegrable_p2ExclError_of_polygonBundle hCp0 hW3 hP4 hlogdrv hmeas h1 h2 hc3 hgm

/-- Regular variation of index `3α` in Case 3, from the cited uncut volume tail. -/
theorem regularlyVarying_two_of_source_volumeTail (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {C : ℝ} (hC : 0 ≤ C) (hVolTail : M.CriticalVolumeTail C) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two_of_hP_of_ae_deriv hα hr₀ hβ hac hmR hae h1 h2 hP
    (M.p2ExclError_tendsto_zero_of_source_volumeTail h1 h2 hP hTri hC₀ hp hF hC hVolTail)

/-- **Proposition I.4.15, Case 3: `E_{β_c,r}|K|² ∼ A r^{3α}`**, with the source-cited uncut
volume tail as the only probabilistic input of the lower comparison. -/
theorem secondMoment_asymptotic_case3_of_source_volumeTail (hα : 0 < M.α) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {C : ℝ} (hC : 0 ≤ C) (hVolTail : M.CriticalVolumeTail C) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨c, Cp, -, -, hCp0, hdrv, hlogdrv, hW3, hP4⟩ :=
    M.exists_repaired_case3_polygon_bundle hC₀ hp hP hTri hF
  obtain ⟨c3, hc3, hgm⟩ := M.exists_momentGap_of_volumeTail_soon hC hVolTail
    (fun t ht => h2 t (le_trans (le_max_right 1 r₀) ht))
  exact M.secondMoment_asymptotic_case3_p21 hα hr₀ hβ hac hae h1 h2 hP hCp0 hW3 hP4 hdrv
    hlogdrv hmeasE2 hmeasEbar hlogH hlogE0 hc3 hgm

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_momentGap_of_volumeTail_soon
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_source_volumeTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_source_volumeTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_source_volumeTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_source_volumeTail
