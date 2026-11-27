/-
Ultramath swarm `smwzlje3f`, member `m3`, direction `d2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f` with m3/m7 sources.
Integration based on production commit `caf06cb0a9face27c4dce7b4a13703d40d4568ac`.

# Composition: the Case-3 consumer with both the radial and the first-moment inputs gone

Two independently checked reductions of `secondMoment_asymptotic_case3_of_source_p21` are
combined here.

* `Smwzlje3fM7.SourceModelData.secondMoment_asymptotic_case3_of_source_p21_no_ac`
  (member `m7`, direction `d3`) removes `hac`, `hae`, `h1`, `hmR`, `hmeasE2`, `hmeasEbar`.
* `SourceModelData.case3_firstMoment_inputs_of_source` (this member, direction `d2`)
  produces `hP`, `hlogH`, `hlogE0` from the source model.

Composing them leaves the Case-3 first-order asymptotic with retained inputs

`r₀ > 0`, `β_c > 0`, the second cutoff moment on a tail, the triangle condition, the
open-triangle radial log bound (Lemma I.4.13), the moment gap, the radius `a₀` with the
continuity of the flux, of `K'` and of the excluded scalar above it, and
`E_{β_c}|K| = ∞`.

Nothing else.  In particular `hα` is the structure field `M.hα`, `h1` follows from `h2`,
`hP`/`hlogH` are Proposition I.4.2 Case 3, `hlogE0` is unconditional, and the second-moment
AC/AE data is the corner-identity package of member `m7`.

Scope: Proposition I.4.15 Case 3 and the regularly-varying half of it.  Not I.4.20, not
Cases 1–2, and no claim that `hgm` is discharged.
-/

module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.FirstMomentSource
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.ACAE

/-! # Combined first-moment and radial Case-3 consumer -/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **Proposition I.4.15, Case 3, with the radial and first-moment inputs discharged.** -/
theorem secondMoment_asymptotic_case3_p21_of_model
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {a₀ : ℝ}
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  have hA₀ : a₀ ≤ max a₀ r₀ := le_max_left a₀ r₀
  have hAr : r₀ ≤ max a₀ r₀ := le_max_right a₀ r₀
  obtain ⟨hP, hlogH, hlogE0⟩ := M.case3_firstMoment_inputs_of_source (a₀ := max a₀ r₀) hβ
    (fun t ht => h2 t (le_trans hAr ht))
    (fun y r hr => hcontinf y r (le_trans hA₀ hr))
    (fun r hr => hK r (le_trans hA₀ hr))
    (fun r hr => hex r (le_trans hA₀ hr))
    htop hTri hC₀ hp hF
  exact Smwzlje3fM7.SourceModelData.secondMoment_asymptotic_case3_of_source_p21_no_ac M M.hα
    hr₀ (ne_of_gt hβ) h2 hP hTri hC₀ hp hF hlogH hlogE0 hc3 hgm

/-- **The regularly-varying half of Proposition I.4.15, Case 3, with the radial and
first-moment inputs discharged.** -/
theorem regularlyVarying_two_p21_of_model
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (0 : ℝ) < M.betaCrit)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {a₀ : ℝ}
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  have hA₀ : a₀ ≤ max a₀ r₀ := le_max_left a₀ r₀
  obtain ⟨hP, -, -⟩ := M.case3_firstMoment_inputs_of_source (a₀ := max a₀ r₀) hβ
    (fun t ht => h2 t (le_trans (le_max_right a₀ r₀) ht))
    (fun y r hr => hcontinf y r (le_trans hA₀ hr))
    (fun r hr => hK r (le_trans hA₀ hr))
    (fun r hr => hex r (le_trans hA₀ hr))
    htop hTri hC₀ hp hF
  exact Smwzlje3fM7.SourceModelData.regularlyVarying_two_of_source_p21_no_ac M M.hα
    hr₀ (ne_of_gt hβ) h2 hP hTri hC₀ hp hF hc3 hgm

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_p21_of_model
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_p21_of_model
