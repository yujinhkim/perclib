/-
Ultramath swarm `smwzlje3f`, member `m7`, direction `d3`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m7/TailRoute.lean`.

# Case 3 of Proposition I.4.15 from the open-triangle tail alone

`exists_repaired_case3_polygon_bundle` uses the pointwise log-radial bound `hF` (Lemma I.4.13)
only twice: to conclude that the driver `∇_{r^c} + r^{-c}` vanishes and that it is logarithmically
integrable (`case3Driver_isLogErrorFunction`).  Both are *conclusions* of Lemma I.4.3; the second
is needed only for the sharp constant `E_{β_c,r}|K|² ∼ A r^{3α}`, while the first — the vanishing
of the driver — is all that the Case-3 error estimate `E_{2,r} → 0` and hence the regular variation
of index `3α` consume.

This file therefore records the *strictly weaker* input under which the first clause of
Proposition I.4.15 holds in Case 3: the vanishing of the open-triangle tail
`∇_r = (M.nablaTail r).toReal → 0`, which is precisely the second component of the
`IsLogErrorFunction` produced by Lemma I.4.3 and which under `(HD)(3)` is supplied by production
(`isLogErrorFunction_nablaTail_of_HD_case2_or_case3`).

* `tendsto_case3Driver_zero_of_tail` — `∇_r → 0` implies `∇_{r^c} + r^{-c} → 0`;
* `exists_case3_bundle_of_tail` — the repaired polygon bundle with the log-integrability conjunct
  dropped and its two driver conjuncts replaced by `∇_r → 0`;
* `p2ExclError_tendsto_zero_of_tail`, `regularlyVarying_two_of_source_p21_of_tail`,
  `rv2_momOf_cutProb_of_tail` — `E_{2,r} → 0`, regular variation of `r ↦ E_{β_c,r}|K|²` of index
  `3α`, and its `momOf` form used by Proposition I.4.20;
* `case3_moment_three_asymptotic_of_HD_case3_no_hRV2` — the `p = 3` second induction of
  Proposition I.4.20 with its second-moment regular-variation input `hRV2` **derived**, and no
  hypothesis added relative to `I420Case3.case3_moment_three_asymptotic_of_HD_case3`.

No `sorry`, `admit`, `native_decide`, `sorryAx` or custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Repaired
public import PercLib.CriticalLRP.Analysis.OpenTriangleLogTail
public import PercLib.CriticalLRP.Analysis.LogScaling
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.RatioInduction.Asymptotic
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.ACAE

/-! # The triangle-tail route to Case 3 -/

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

/-- **`r ↦ r ^ (-c)` is logarithmically integrable** for `c > 0`: `∫ r ^ (-c) dr/r = ∫ r ^ (-c-1)`
converges at infinity. -/
theorem logIntegrable_rpow_neg {c : ℝ} (hc : 0 < c) :
    Analysis.LogarithmicallyIntegrable (fun r : ℝ => r ^ (-c)) := by
  refine ⟨?_, 1, one_pos, ?_⟩
  · fun_prop
  · refine (integrableOn_Ioi_rpow_of_lt (a := -c - 1) (c := (1 : ℝ)) (by linarith) one_pos).congr_fun
      ?_ measurableSet_Ioi
    intro r hr
    have hrpos : (0 : ℝ) < r := lt_trans one_pos hr
    have h1 : (0 : ℝ) < r ^ (-c) := Real.rpow_pos_of_pos hrpos _
    change r ^ (-c - 1) = |r ^ (-c)| / r
    rw [abs_of_pos h1, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hrpos]
    ring_nf

namespace SourceModelData

variable (M : SourceModelData)

/-- **The Case-3 driver vanishes as soon as the open-triangle tail does.**
`M.case3Driver c r = (M.nablaTail (r ^ c)).toReal + r ^ (-c)`, and `r ↦ r ^ c → ∞` for `c > 0`. -/
theorem tendsto_case3Driver_zero_of_tail {c : ℝ} (hc : 0 < c)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0)) :
    Tendsto (M.case3Driver c) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) atTop (𝓝 0) :=
    hTail.comp (tendsto_rpow_atTop hc)
  have h2 : Tendsto (fun r : ℝ => r ^ (-c)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hc
  change Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal + r ^ (-c)) atTop (𝓝 0)
  simpa only [zero_add] using h1.add h2

/-- **The repaired Case-3 polygon bundle from the open-triangle tail.**

This is `exists_repaired_case3_polygon_bundle` with the pointwise log-radial bound `hF` replaced by
the vanishing of the open-triangle tail, and with the driver's logarithmic integrability dropped
(it is used only for the sharp constant).  The windowed `ℓ = 3` gap and the `ℓ = 4` polygon bound
come from the triangle condition and the first-moment asymptotic, exactly as there. -/
theorem exists_case3_bundle_of_tail
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0)) :
    ∃ c Cp : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 < Cp ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      M.WindowedEllThreeGap c Cp ∧
      (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
        I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
          ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) := by
  have hβ : 0 < (M.betaCrit : ℝ) := I418C.ChiInput.betaCrit_pos_of_tendsto_chi_div M hP
  obtain ⟨c₀, hc₀, hχu⟩ := I418C.ChiInput.exists_chi_lower_uniform_and_finite M hβ hP
  have hχfin : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤ :=
    fun r hr => (hχu r (by linarith)).2
  have hdpos : (0 : ℝ) < (M.d : ℝ) := by exact_mod_cast M.hd
  obtain ⟨c, hcpos, hcle, hcα⟩ :
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ c ≤ M.α / (2 * (M.d : ℝ)) :=
    ⟨min (M.α / (2 * (M.d : ℝ))) (1 / 2),
      lt_min (div_pos M.hα (by positivity)) (by norm_num),
      min_le_right _ _, min_le_left _ _⟩
  obtain ⟨Cp₃, -, hW⟩ := M.exists_windowedEllThreeGap hcpos hcle hTri hχfin
  obtain ⟨Knear, hKnear, hnear⟩ := I418C.NearBall.exists_near_ball M
  have hB2hB3hlink := M.hB2_hB3_hlink_derived hTri
  obtain ⟨hB2, hB3, hlink⟩ := hB2hB3hlink
  have hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
        ≤ max 1 (M.triSelf * Knear / c₀) * M.case3Driver c r
            * (M.cutMassAt r 0).toReal := by
    intro r hr x
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
    have hχfinr : M.cutMassAt r 0 ≠ ⊤ := hχfin r hr
    have hχr : c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal := (hχu r hrpos).1
    have hnearR : (1 : ℝ) ≤ r ^ (M.α / (2 * (M.d : ℝ))) :=
      Real.one_le_rpow hr (div_nonneg M.hα.le (by positivity))
    obtain ⟨s, hfar, hcard⟩ := hnear (r ^ (M.α / (2 * (M.d : ℝ)))) hnearR
    have hbound := I418C.source_polygon_bound_tail_cc (c₀ := c₀) (K := Knear)
      (cc := c) (ell := 4) M r (r ^ (M.α / (2 * (M.d : ℝ)))) s hr hc₀ hKnear.le
      hχfinr hTri hB2 hB3 hlink
      (by norm_num) hcα hfar hcard rfl hχr x
    have hpow : (M.cutMassAt r 0).toReal ^ (4 - 3) = (M.cutMassAt r 0).toReal := by norm_num
    rw [hpow] at hbound
    exact hbound
  refine ⟨c, max Cp₃ (max 1 (M.triSelf * Knear / c₀)), hcpos, hcle,
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) (le_max_right _ _)),
    tendsto_case3Driver_zero_of_tail M hcpos hTail, ?_, ?_⟩
  · intro r hr
    refine (hW r hr).trans ?_
    have h1 : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
    have hle : Cp₃ ≤ max Cp₃ (max 1 (M.triSelf * Knear / c₀)) := le_max_left _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h1) h2
  · intro r hr x
    refine (hpoly4 r hr x).trans ?_
    have h2 : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
    have h3 : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
    have hle : max 1 (M.triSelf * Knear / c₀)
        ≤ max Cp₃ (max 1 (M.triSelf * Knear / c₀)) := le_max_right _ _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle h2) h3

/-- **Case 3: `E_{2,r} → 0` from the vanishing of the open-triangle tail.** -/
theorem p2ExclError_tendsto_zero_of_tail {r₀ : ℝ}
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  obtain ⟨c, Cp, hc0, -, hCp0, hdrv, hW3, hP4⟩ := exists_case3_bundle_of_tail M hP hTri hTail
  have h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤ :=
    fun t ht => M.cutMoment_one_ne_top_of_two (h2 t ht)
  exact M.p2ExclError_tendsto_zero_of_polygonBundle hCp0 hW3 hP4 hdrv h1 h2 hc3 hgm

/-- **Logarithmic integrability of the Case-3 driver from that of the open-triangle tail**:
`M.case3Driver c r = (M.nablaTail (r ^ c)).toReal + r ^ (-c)`, the first summand by Lemma I.4.19
(`logarithmicallyIntegrable_comp_rpow_const_mul`), the second by `logIntegrable_rpow_neg`. -/
theorem logIntegrable_case3Driver_of_logTail {c : ℝ} (hc : 0 < c)
    (hlog : Analysis.LogarithmicallyIntegrable (fun r : ℝ => (M.nablaTail r).toReal)) :
    Analysis.LogarithmicallyIntegrable (M.case3Driver c) := by
  have h1 : Analysis.LogarithmicallyIntegrable
      (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) := by
    simpa using Analysis.logarithmicallyIntegrable_comp_rpow_const_mul
      (fun r : ℝ => (M.nablaTail r).toReal) hlog hc one_pos
  have h2 : Analysis.LogarithmicallyIntegrable (fun r : ℝ => r ^ (-c)) :=
    logIntegrable_rpow_neg hc
  exact VolumeMoments.FirstMoment.logIntegrable_add h1 h2

/-- **Proposition I.4.15, Case 3, the sharp constant**: `E_{β_c,r}|K|² ∼ A r^{3α}` from the
triangle condition, the logarithmic integrability and vanishing of the open-triangle tail
(Lemma I.4.3's conclusion, no pointwise bound), the first-moment asymptotic and the moment gap.
The `p = 2` bundle is supplied by `exists_case3_bundle_of_tail` and the driver's logarithmic
integrability by `logIntegrable_case3Driver_of_logTail`; `hac`, `hae`, `h1`, `hmR`, `hmeasE2`,
`hmeasEbar` are discharged in `ACAE.lean`. -/
theorem secondMoment_asymptotic_case3_p21_of_logTail
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {c Cp : ℝ} (hc : 0 < c) (hCp : 0 < Cp)
    (hW3 : M.WindowedEllThreeGap c Cp)
    (hP4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x
        ≤ Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)
    (hdrv : Tendsto (M.case3Driver c) atTop (𝓝 0))
    (hlogNabla : Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal))
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  have hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c) :=
    logIntegrable_case3Driver_of_logTail M hc hlogNabla.1
  exact secondMoment_asymptotic_case3_p21_no_ac M hα hr₀ hβ h2 hP hCp hW3 hP4 hdrv hlogdrv
    hlogH hlogE0 hc3 hgm

/-- **Proposition I.4.15, Case 3 from the source's own second-clause hypothesis**: the triangle
condition and `∇_r` logarithmically integrable (with `∇_r → 0`, i.e. Lemma I.4.3's conclusion),
plus Proposition I.4.2's first-moment inputs.  No pointwise log-radial bound and no radial
regularity hypothesis is retained. -/
theorem secondMoment_asymptotic_case3_of_source_of_logTail
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hlogNabla : Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal))
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) := by
  obtain ⟨c, Cp, hc0, -, hCp0, hdrv, hW3, hP4⟩ :=
    exists_case3_bundle_of_tail M hP hTri hlogNabla.2
  exact secondMoment_asymptotic_case3_p21_of_logTail M hα hr₀ hβ h2 hP hc0 hCp0 hW3 hP4
    hdrv hlogNabla hlogH hlogE0 hc3 hgm

/-- **Proposition I.4.15, first clause, Case 3: regular variation of index `3α`** from the
triangle condition, the vanishing of the open-triangle tail, the first-moment asymptotic and the
moment gap — with `hac`, `hae`, `h1`, `hmR` discharged. -/
theorem regularlyVarying_two_of_source_p21_of_tail
    (hα : 0 < M.α) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0))
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
    (p2ExclError_tendsto_zero_of_tail M h2' hP hTri hTail hc3 hgm)

/-- The `hRV2` function of the `p = 3` induction of Proposition I.4.20, from the triangle tail. -/
theorem rv2_momOf_cutProb_of_tail {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) := by
  have h := regularlyVarying_two_of_source_p21_of_tail M M.hα hr₀ hβ h2 hP hTri hTail hc3 hgm
  simpa only [I420Case3.momOf_cutProb_eq_toReal_cutMoment] using h

end SourceModelData

open PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- **The `p = 3` second induction of Proposition I.4.20 with `hRV2` derived — nothing added.**

This has exactly the hypotheses of `I420Case3.case3_moment_three_asymptotic_of_HD_case3` except
that its second-moment regular-variation input `hRV2` is removed: it is Proposition I.4.15,
Case 3 (`rv2_momOf_cutProb_of_tail`), with the triangle tail supplied by
`isLogErrorFunction_nablaTail_of_HD_case2_or_case3` from `(HD)(3)` — the same instance the
I.4.20 Case-3 scope wrapper itself uses — and with the radial AC/AE inputs discharged in
`ACAE.lean`.  Tail finiteness of the second cutoff moment is derived from the root-moment range
`hMa` at `ℓ = 1`, and the I.4.15 spelling of the moment gap from the I.4.20 spelling. -/
theorem case3_moment_three_asymptotic_of_HD_case3_no_hRV2 (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c) (hαd : M.α < (M.d : ℝ))
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hβ : (0 : ℝ) < M.betaCrit) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
    (hmommeas1 : Measurable (fun r =>
      I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r))
    (hmommeas2 : Measurable (fun r =>
      I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r))
    (hRV1 : Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α)
    {cr : ℝ → ℝ}
    (hderivId : ∀ r : ℝ, 0 < r → HasDerivAt
      (fun s => I420Case3.momOf (fun s => M.cutProb s) (0 : M.V) 3 s)
      (cr r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset) r)
    (hcT : Tendsto (fun r => r * cr r *
      I420Case3.ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
        I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 1 r) atTop (𝓝 M.α)) :
    Tendsto (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 3 r /
        mixedMoment 3 (fun m r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) m r) r)
        atTop (𝓝 1) ∧
      Analysis.RegularlyVaryingAtTop
        (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 3 r)
        ((2 * (3 : ℝ) - 1) * M.α) := by
  -- the second cutoff moment is finite on the tail, from the root moment range at `ℓ = 1`
  have h2 : ∀ t : ℝ, max r₀ 1 ≤ t → M.cutMoment 2 t ≠ ⊤ := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
    have hpow := hMa t ht1 1 (by norm_num)
    rwa [M.powMomentAt_cutProb_eq_cutMoment] at hpow
  -- the I.4.15 spelling of the moment gap
  have hgm' : ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal := by
    filter_upwards [hgm] with r hr
    simpa only [I420Case3.momOf_cutProb_eq_toReal_cutMoment,
      M.cutMassAt_zero_eq_cutMoment] using hr
  -- the first-moment asymptotic, exactly as the I.4.20 Case-3 wrapper derives it
  have hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1) :=
    I42C.first_moment_asymptotic_of_rpow_lower M hc hαd hlow hfin hβ hr₀ hderiv hpos hode
      hmeas hhedge h0
  -- Lemma I.4.3 under `(HD)(3)`: the open-triangle tail vanishes
  have hTail : Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0) :=
    (M.isLogErrorFunction_nablaTail_of_HD_case2_or_case3 (Or.inr hHD3)).2
  -- Proposition I.4.15, Case 3
  have hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => I420Case3.momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) :=
    SourceModelData.rv2_momOf_cutProb_of_tail M
      (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      (ne_of_gt hβ) h2 hP hTri hTail hc3 hgm'
  -- the two Case-3 decorrelation limits of Proposition I.4.20
  obtain ⟨hAend, hAmid⟩ :=
    I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3 M hHD3 hTri hc hαd hlow hfin
      hβ hr₀ hderiv hpos hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 3 (by norm_num) hθ0 hθ1 hMa hc3 hgm
  exact PercLib.CriticalLRP.VolumeMoments.HigherMoments.case3_moment_three_asymptotic
    M hAend hAmid
    (I420Case3.momOf_cutProb_pos_three M hMa) hmommeas1 hmommeas2 hRV1 hRV2 hderivId hcT

end PercLib.CriticalLRP.Orchestration.Smwzlje3fM7

/-! ## Axiom audit -/

#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.tendsto_case3Driver_zero_of_tail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.exists_case3_bundle_of_tail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.p2ExclError_tendsto_zero_of_tail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.regularlyVarying_two_of_source_p21_of_tail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.logIntegrable_rpow_neg
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.logIntegrable_case3Driver_of_logTail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.secondMoment_asymptotic_case3_p21_of_logTail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.secondMoment_asymptotic_case3_of_source_of_logTail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.SourceModelData.rv2_momOf_cutProb_of_tail
#print axioms
  PercLib.CriticalLRP.Orchestration.Smwzlje3fM7.case3_moment_three_asymptotic_of_HD_case3_no_hRV2
