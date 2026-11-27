/-
Ultramath swarm `smwzlje3f`, member `m7`, direction `d3`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f` with m3/m7 sources.
Integration based on production commit `caf06cb0a9face27c4dce7b4a13703d40d4568ac`.

# The Case-3 second-moment consumer with its radial-regularity inputs discharged

`PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer` proves Proposition
I.4.15, Case 3 from the paper's hypotheses plus the proved `(2,1)` product gap, but it still takes
the three *radial* inputs of the `p = 2` ODE

```
hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval (fun r => (M.cutMoment 2 r).toReal) r₀ R
hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
        HasDerivAt (fun r => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t
hmR : Measurable M.rhsScalarTwo
```

as hypotheses (and `h1`, `hmeasE2`, `hmeasEbar` as further bookkeeping inputs).

Those are not model assumptions.  This file derives them from the already-proved off-corner
radius calculus:

* the integrated radius identity on every corner-containing window
  (`SmwywszgoM5.integral_rhsScalarTwo_eq_sub_of_cornerRadii`, from the off-corner identity
  `M.integral_rhsScalarTwo_eq_sub_of_offCornerWindow` plus finiteness of the corner set),
* its packaging `SmwywszgoM5.ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii_tail_no_meas`
  (absolute continuity and the a.e. derivative `M.rhsScalarTwo` on the far tail),

whose only non-model input is a monotone edge-exhausting family `S : ℕ → Finset (Sym2 M.V)`.
That family is constructed here from countability of `M.V = Fin M.d → ℤ`
(`Smwzlje3fM7.SourceModelData.exists_windowFinsets`), so it disappears as well.

## Results

* `Smwzlje3fM7.SourceModelData.ac_and_ae_toReal_two_farTail` — there is a radius `r₁` such that on
  every tail `[r₀, ∞)` with `r₁ ≤ r₀`, the second cutoff moment is absolutely continuous on each
  window and has derivative `M.rhsScalarTwo` almost everywhere, the *only* remaining input being
  tail finiteness of the second cutoff moment.
* `...secondMoment_asymptotic_case3_p21_no_ac` and
  `...secondMoment_asymptotic_case3_of_source_p21_no_ac` — the bundle-level and source-level
  Case-3 conclusions with `hac`, `hae`, `hmR`, `h1`, `hmeasE2`, `hmeasEbar` all removed and
  **nothing added**: `h1` follows from `h2` (`M.cutMoment_one_ne_top_of_two`), the three
  measurabilities from `h1`, `h2` (`measurable_rhsScalarTwo_of_tail`,
  `measurable_p2ExclError_of_tail`, `measurable_p2Ebar_of_tail`), and `hac`, `hae` from the far
  tail beyond the model's own coefficient-bound threshold.
* `...regularlyVarying_two_of_source_p21_no_ac` — the same for regular variation of index `3α`.

The retained inputs of the source-level theorem are exactly

`hα`, `hβ`, `h2`, `hP`, `hTri`, `hF`, `hlogH`, `hlogE0`, `hgm`,

i.e. the source's parameters, the tail finiteness of the second cutoff moment, Props I.4.2 /
I.4.13 / I.4.15's first-moment and triangle inputs, the two first-moment logarithmic
integrabilities, and the moment gap.  The numerator/gap hypotheses of Case 3 are still consumed
through `ProductGap`; no `hgap`, no `q = 0` star, no finite-volume substitute appears here.

No `sorry`, `admit`, `native_decide`, `sorryAx` or custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCornerIdentity
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.Defs

/-! # Case 3 without the radial-regularity hypotheses -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.Smwzlje3fM7

namespace SourceModelData

variable (M : SourceModelData)

/-! ## The radial picture with the window family constructed -/

/-- **`hac` and `hae` of the Case-3 consumer from tail finiteness alone.**

There is a radius `r₁` such that for every `r₀ ≥ r₁` with `r₀ > 0`, tail finiteness of the second
cutoff moment on `[r₀, ∞)` gives

* `r ↦ (M.cutMoment 2 r).toReal` is absolutely continuous on `[r₀, R]` for every `R ≥ r₀`;
* its radius derivative is `M.rhsScalarTwo` almost everywhere on `[r₀, ∞)`.

Proof: `SmwywszgoM5.ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii_tail_no_meas` beyond the
model's own coefficient-bound threshold `r₁` (`exists_coeffRHS_bound_of_deriv_decay`), with the
monotone edge-exhausting family supplied by `M.exists_windowFinsets`. -/
theorem ac_and_ae_toReal_two_farTail :
    ∃ r₁ : ℝ, ∀ {r₀ : ℝ}, r₁ ≤ r₀ → 0 < r₀ →
      (∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) →
      (∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
        (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R) ∧
      (∀ᵐ t ∂(volume.restrict (Ici r₀)),
        HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t) := by
  obtain ⟨r₁, h⟩ :=
    SmwywszgoM5.ac_and_ae_hasDerivAt_toReal_two_of_cornerRadii_tail_no_meas M
  obtain ⟨S, hSmono, hS⟩ := exists_windowFinsets M
  exact ⟨r₁, fun hle h0 h2 => h hle h0 h2 S hSmono hS⟩

/-! ## The `ProductGap` bundle consumer without `hac`, `hae`, `h1`, `hmR`, `hmeasE2`, `hmeasEbar` -/

/-- **Case 3 of Proposition I.4.15 in `ProductGap` bundle vocabulary, without radial inputs.**

Compared with `SourceModelData.secondMoment_asymptotic_case3_p21` the hypotheses `hac`, `hae`,
`h1`, `hmeasE2`, `hmeasEbar` are gone and nothing is added: `h1` is `h2`'s first moment
(`M.cutMoment_one_ne_top_of_two`), the two error measurabilities are `h1`, `h2`
(`measurable_p2ExclError_of_tail`, `measurable_p2Ebar_of_tail`), and `hac`, `hae` are
`M.ac_and_ae_toReal_two_farTail` applied at `max r₀ r₁` (the conclusion is a limit at infinity, so
the base point is immaterial). -/
theorem secondMoment_asymptotic_case3_p21_no_ac (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c Cp : ℝ} (hCp : 0 < Cp)
    (hW3 : M.WindowedEllThreeGap c Cp)
    (hP4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
        ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0))
    (hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c))
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨r₁, hAE⟩ := ac_and_ae_toReal_two_farTail M
  have hle : r₀ ≤ max r₀ r₁ := le_max_left _ _
  have ha0 : 0 < max r₀ r₁ := lt_of_lt_of_le hr₀ hle
  have h2' : ∀ t : ℝ, max r₀ r₁ ≤ t → M.cutMoment 2 t ≠ ⊤ :=
    fun t ht => h2 t (le_trans hle ht)
  have h1' : ∀ t : ℝ, max r₀ r₁ ≤ t → M.cutMoment 1 t ≠ ⊤ :=
    fun t ht => M.cutMoment_one_ne_top_of_two (h2' t ht)
  obtain ⟨hac, hae⟩ := hAE (le_max_right _ _) ha0 h2'
  exact M.secondMoment_asymptotic_case3_p21 hα ha0 hβ hac hae h1' h2' hP hCp hW3 hP4 hdrv
    hlogdrv (M.measurable_p2ExclError_of_tail h1' h2') (M.measurable_p2Ebar_of_tail hα h1' h2')
    hlogH hlogE0 hc3 hgm

/-! ## The source-level consumer without radial inputs -/

/-- **Proposition I.4.15, Case 3 from the paper's own hypotheses, with the radial inputs
discharged.**  This is `secondMoment_asymptotic_case3_of_source_p21` with `hac`, `hae`, `h1`,
`hmeasE2`, `hmeasEbar` removed and nothing added; the retained inputs are `hα`, `hβ`, `h2`, `hP`,
`hTri`, `hF`, `hlogH`, `hlogE0`, `hgm`. -/
theorem secondMoment_asymptotic_case3_of_source_p21_no_ac
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨c, Cp, hc0, -, hCp0, hdrv, hlogdrv, hW3, hP4⟩ :=
    M.exists_repaired_case3_polygon_bundle hC₀ hp hP hTri hF
  exact secondMoment_asymptotic_case3_p21_no_ac M hα hr₀ hβ h2 hP hCp0 hW3 hP4 hdrv hlogdrv
    hlogH hlogE0 hc3 hgm

/-- **Regular variation of index `3α` for `r ↦ E_{β_c,r}|K|²`, from the paper's own hypotheses,
with the radial inputs discharged.**  This is `regularlyVarying_two_of_source_p21` with `hac`,
`hae`, `h1`, `hmR` removed and nothing added. -/
theorem regularlyVarying_two_of_source_p21_no_ac
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) := by
  obtain ⟨r₁, hAE⟩ := ac_and_ae_toReal_two_farTail M
  have hle : r₀ ≤ max r₀ r₁ := le_max_left _ _
  have ha0 : 0 < max r₀ r₁ := lt_of_lt_of_le hr₀ hle
  have h2' : ∀ t : ℝ, max r₀ r₁ ≤ t → M.cutMoment 2 t ≠ ⊤ :=
    fun t ht => h2 t (le_trans hle ht)
  have h1' : ∀ t : ℝ, max r₀ r₁ ≤ t → M.cutMoment 1 t ≠ ⊤ :=
    fun t ht => M.cutMoment_one_ne_top_of_two (h2' t ht)
  obtain ⟨hac, hae⟩ := hAE (le_max_right _ _) ha0 h2'
  exact M.regularlyVarying_two_of_hP_of_ae_deriv hα ha0 hβ hac
    (M.measurable_rhsScalarTwo_of_tail h2') hae h1' h2' hP
    (M.p2ExclError_tendsto_zero_of_source_p21 h1' h2' hP hTri hC₀ hp hF hc3 hgm)

end SourceModelData

end PercLib.CriticalLRP.Orchestration.Smwzlje3fM7

/-! ## Axiom audit -/

#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.ac_and_ae_toReal_two_farTail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.secondMoment_asymptotic_case3_p21_no_ac
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.secondMoment_asymptotic_case3_of_source_p21_no_ac
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.regularlyVarying_two_of_source_p21_no_ac
