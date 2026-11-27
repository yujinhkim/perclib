/-
Proposition I.4.15, Case 3, with the `ℓ = 3` numerator gap closed in windowed form.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m6`, direction `d6`.

`SecondMomentCase3.secondMoment_asymptotic_case3` concludes

  `∃ A > 0, E_{β_c,r}|K|² / r^{3α} → A`

from the Case-3 input bundle `hcase3`, which contains the *per-vertex* `ℓ = 3` polygon
bound — refuted in `NoGo.lean`.  This file restates the same theorem with the windowed
`ℓ = 3` input (`Defs.WindowedEllThreeGap`), proves it, and then discharges the whole bundle
from the paper's own hypotheses by `Repaired.exists_repaired_case3_polygon_bundle`.

The remaining numerator input is exactly `hgap`, the per-vertex Lemma I.4.17 at `p = 3`,
`q = 0` (`E[|K_0|³ 1(y ∈ K_0)] ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³`), which is *not* touched
here.  The combinatorial coefficients `C₃, C₄` and the source's `7 = 2p + 2q + 1` are used
unchanged.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Consumer
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Repaired

/-! # The Case-3 second-moment asymptotic with the windowed `ℓ = 3` input -/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **Proposition I.4.15, Case 3, with the windowed `ℓ = 3` polygon input.**

Identical to `secondMoment_asymptotic_case3` except that the `ℓ = 3` conjunct of the bundle
is the windowed bound `M.WindowedEllThreeGap c Cp`, which `Windowed.lean` proves from the
triangle condition and the ball count. -/
theorem secondMoment_asymptotic_case3_windowed (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hcase3 : ∃ c Cp : ℝ, 0 < c ∧ 0 < Cp ∧ M.Case3PolygonBundleWindowed c Cp)
    {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
            * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y
            * (M.cutMassAt r 0).toReal ^ 3)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨c, Cp, hc0, hCp0, hdrv, hlogdrv, hT3sum, hpoly4⟩ := hcase3
  have hcn : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤ := hc
  have hnum := M.connCubeMass_toReal_le_of_windowedGap (c := c) (Cp := Cp)
    hC3 hC4 hgap hT3sum hpoly4 hcn
  refine M.tendsto_div_two_of_case3 hα hr₀ hβ hac hae h1 h2 hP
    (K := (C3 + C4) * Cp) (c := c) (c3 := c3) (by positivity) hc3 hc hnum hgm
    hdrv hlogdrv hmeasE2 hmeasEbar hlogH hlogE0

/-- **Proposition I.4.15, Case 3, from the paper's own hypotheses.**

The polygon bundle is discharged by `exists_repaired_case3_polygon_bundle`; every remaining
hypothesis is a source object: the first-moment asymptotic `hP` (Proposition I.4.2), the
triangle condition `hTri` (`∇_{β_c} < ∞`), the open-triangle log-radial bound `hF`
(Lemma I.4.13), the two canonical moment inputs `h1`, `h2`, the Case-3 ODE data, and the
moment gap `hgm`.  The per-vertex `ℓ = 3` bound is never assumed. -/
theorem secondMoment_asymptotic_case3_of_source (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
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
    {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgap : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
            * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y
            * (M.cutMassAt r 0).toReal ^ 3)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨c, Cp, hc0, -, hCp0, hdrv, hlogdrv, hW, hpoly4⟩ :=
    M.exists_repaired_case3_polygon_bundle hC₀ hp hP hTri hF
  exact M.secondMoment_asymptotic_case3_windowed hα hr₀ hβ hac hae h1 h2 hP
    ⟨c, Cp, hc0, hCp0, hdrv, hlogdrv, hW, hpoly4⟩ hC3 hC4 hc hgap
    hmeasE2 hmeasEbar hlogH hlogE0 hc3 hgm

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
