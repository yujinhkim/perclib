/-
Ultramath swarm `smwziumdb`, member `m5`, direction `d2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`, member `m5`.
Product-numerator integration based on production commit `e59e9347a3988d8c181ba0308758fa84fc2ec15f`.

# Proposition I.4.15 Case 3 from the paper's own hypotheses, with no star input

`Main.lean` proves the Case-3 consumer from the windowed polygon bundle
(`M.PolygonWindowInputs`).  Here the bundle is discharged by production's
`M.exists_repaired_case3_polygon_bundle`, so every remaining hypothesis is one of the paper's own
inputs: the ODE regularity of `r ↦ E_{β_c,r}|K|²`, finiteness of the first two cutoff moments,
the first-moment asymptotic `hP` (Proposition I.4.2), the triangle condition `hTri`, the
open-triangle log-radial bound `hF` (Lemma I.4.13), the moment gap `c₃(E|K|)³ ≤ E|K|²`, and the
measurablility / logarithmic-integrability obligations `hmeasE2`, `hmeasEbar`, `hlogH`, `hlogE0`.

Compared with `SecondMomentCase3.secondMoment_asymptotic_case3_windowed` (or
`secondMoment_asymptotic_case3_of_source`) the hypotheses

* `hc : ∀ r ≥ 1, M.connCubeMass r ≠ ⊤` (the `q = 0` star is finite), and
* `hgap : ∀ r ≥ 1, ∀ y ∈ B_r, E[|K_0|³ 1(y ∈ K_0)] ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³`

are **absent**: they are replaced by the *proved* `p = 2`, `q = 1` product gap
(`I417Example.printed_le`, i.e. `I417_p21_source_tsub_le_excess` plus its landed tree
evaluation) applied at the swapped pair `(y,0)`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.Main

/-! # Case-3 product route from the retained source hypotheses -/

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology Set
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **`𝓔_{2,r} → 0` in Case 3, from the paper's hypotheses and the `(2,1)` product gap.** -/
theorem p2ExclError_tendsto_zero_of_source_p21 {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  obtain ⟨c, Cp, hc0, -, hCp0, hdrv, hlogdrv, hW3, hP4⟩ :=
    M.exists_repaired_case3_polygon_bundle hC₀ hp hP hTri hF
  exact M.p2ExclError_tendsto_zero_of_polygonBundle hCp0 hW3 hP4 hdrv h1 h2 hc3 hgm

/-- **Logarithmic integrability of `𝓔_{2,r}` in Case 3, from the paper's hypotheses and the
`(2,1)` product gap.** -/
theorem logIntegrable_p2ExclError_of_source_p21 {r₀ : ℝ}
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hmeas : Measurable M.p2ExclError)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  obtain ⟨c, Cp, hc0, -, hCp0, hdrv, hlogdrv, hW3, hP4⟩ :=
    M.exists_repaired_case3_polygon_bundle hC₀ hp hP hTri hF
  exact M.logIntegrable_p2ExclError_of_polygonBundle hCp0 hW3 hP4 hlogdrv hmeas h1 h2 hc3 hgm

/-- **Proposition I.4.15, Case 3, from the paper's own hypotheses**: with the `(2,1)` product gap
replacing the `p = 3`, `q = 0` star, `r ↦ E_{β_c,r}|K|²` is regularly varying of index `3α`. -/
theorem regularlyVarying_two_of_source_p21 (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
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
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two_of_hP_of_ae_deriv hα hr₀ hβ hac hmR hae h1 h2 hP
    (M.p2ExclError_tendsto_zero_of_source_p21 h1 h2 hP hTri hC₀ hp hF hc3 hgm)

/-- **Proposition I.4.15, Case 3: `E_{β_c,r}|K|² ∼ A r^{3α}`**, from the paper's own hypotheses
and the `(2,1)` product gap. -/
theorem secondMoment_asymptotic_case3_of_source_p21 (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
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
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨c, Cp, hc0, -, hCp0, hdrv, hlogdrv, hW3, hP4⟩ :=
    M.exists_repaired_case3_polygon_bundle hC₀ hp hP hTri hF
  exact M.secondMoment_asymptotic_case3_p21 hα hr₀ hβ hac hae h1 h2 hP hCp0 hW3 hP4 hdrv
    hlogdrv hmeasE2 hmeasEbar hlogH hlogE0 hc3 hgm

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
