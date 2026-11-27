/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m7`, direction d10.

# Clean audit file for `Case3Bundle`

This file is compiled **against the current production interface** and (i) prints the exact type of
every production helper that `Case3Bundle` consumes, (ii) prints the exact type and the axiom
dependencies of every theorem `Case3Bundle` exports, and (iii) adds the two *constant-accounting*
wrappers in which every constant of the Case-3 numerator (`C₃`, `C₄`, `c₃`, `Cp`, `c`) is displayed
as **existential outer data** rather than as an arbitrary input pair.

Compile from `repo/.scratch/critical-lrp-orchestration` (this directory has to be put on `LEAN_PATH`
because the Lake search path is the package's):

```
lake env bash -c 'LEAN_PATH=<member dir>:$LEAN_PATH lean \
  -DwarningAsError=true -DautoImplicit=false -Dweak.linter.mathlibStandardSet=true \
  <member dir>/Case3Audit.lean'
```

## What is validated where

* **Core results (no normalization input).**  The two-scale window bound for `T^3`, the ball-count
  rate `|B_{√r}|/|B_r| = O(r^{-d/2})`, the windowed `ell = 3` clause, the numerator bound and the
  `E_{2,r}` bound/vanishing/log-integrability all take only: `hP` (Prop I.4.2), `∇ < ∞`, the
  log-error form of `∇_·`, tail finiteness of `E|K|` and `E|K|²`, `hgap`, the moment gap, and the
  two measurability obligations.  They never use the per-vertex `hT3`.
* **Normalization assembly.**  `tendsto_div_two_of_case3_windowed` is a *wrapper* around the
  existing production `M.tendsto_div_two`; its extra hypotheses (`hac`, `hae`, `h1`, `h2`,
  `hmeasEbar`, `hlogH`, `hlogE0`, `H_r → 0`) are exactly the normalization inputs of that existing
  theorem, not new content and not consequences of the windowed bound.  The wrapper is *not*
  needed for the `E_{2,r}` conclusions and adds nothing to them.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3Bundle

-- `#print` and long type lines are the point of this audit file
set_option linter.hashCommand false
set_option linter.style.longLine false

/-! # Exact types of the production helpers consumed -/

#print PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2Ebar
#print PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_div_two
#print PercLib.CriticalLRP.Orchestration.SourceModelData.exists_polygonBound_four
#print PercLib.CriticalLRP.I418C.ChiInput.exists_chi_lower_uniform_and_finite
#print PercLib.CriticalLRP.I420Case3.one_le_polyK_three_of_chi_ne_top
#print PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_connCubeMass_div
#print PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_eq_sum_vertex
#print PercLib.CriticalLRP.Orchestration.SourceModelData.cutTriPoint_le_triPoint
#print PercLib.CriticalLRP.Orchestration.SourceModelData.triPoint_le_self
#print PercLib.CriticalLRP.Orchestration.SourceModelData.triPoint_le_nablaTail
#print PercLib.CriticalLRP.Orchestration.SourceModelData.ball_count
#print PercLib.CriticalLRP.Analysis.isLogErrorFunction_nablaTail_add_rpow_neg

/-! # Exact types of the exported theorems -/

#print PercLib.CriticalLRP.Orchestration.SourceModelData.sum_polyK_three_ballF_le_two_scale
#print PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_sum_polyK_three_ballF_le_rate
#print PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_of_windowed_ell_three
#print PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_of_windowed_ell_three
#print PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_windowed_ell_three
#print PercLib.CriticalLRP.Orchestration.SourceModelData.not_forall_polyK_three_le_case3Driver_of_tendsto
#print PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3_bundle
#print PercLib.CriticalLRP.Orchestration.SourceModelData.exists_repaired_case3_bundle
#print PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_div_two_of_case3_windowed

/-! # Constant accounting: every constant displayed as existential outer data -/

noncomputable section

@[expose] public section

open MeasureTheory Measure ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Asymptotics

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The Case-3 error with all constants existentially quantified.**

There are `C > 0` and `c > 0` such that

  `E_{2,r} ≤ C * ((∇_{r^c} + r^{-c}) + ∇_{√r} + r^{-d/2} ∇(0,0))` eventually,

and the driver vanishes.  The numerator constants `C₃, C₄` (Lemma I.4.17) and the moment-gap
constant `c₃` are inputs as existential data, not as arbitrary reals; the cut-off first moment's
finiteness constant `c₀` produced by `exists_chi_lower_uniform_and_finite` is internal and never
appears in the conclusion.  Apart from the existential constants the hypotheses are exactly:
`hP`, `∇ < ∞`, the log-error form of `∇_·`, tail finiteness of `E|K|` and `E|K|²`, `hgap` and the
moment gap. -/
theorem exists_case3_error_rate
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hTail : Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal))
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcM : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgm : ∃ c₃ : ℝ, 0 < c₃ ∧
      ∀ᶠ r : ℝ in atTop, c₃ * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hgap : ∃ C3 C4 : ℝ, 0 ≤ C3 ∧ 0 ≤ C4 ∧ ∀ r : ℝ, 1 ≤ r →
      ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 / 2 ∧
      Tendsto (M.case3Driver c) atTop (𝓝 0) ∧
      ∀ᶠ r : ℝ in atTop,
        M.p2ExclError r
          ≤ C * (M.case3Driver c r + (M.nablaTail (Real.sqrt r)).toReal
              + r ^ (-(M.d : ℝ) / 2) * M.triSelf) := by
  obtain ⟨c₃, hc₃, hgmr⟩ := hgm
  obtain ⟨C3, C4, hC3, hC4, hgapr⟩ := hgap
  obtain ⟨c, Cp, hc, hCp, hT4⟩ := M.exists_polygonBound_four hP hTri
  set c' : ℝ := min c (1 / 2) with hc'_def
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc'2 : c' ≤ 1 / 2 := min_le_right _ _
  have hc'c : c' ≤ c := min_le_left _ _
  have hT4' : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c' r * (M.cutMassAt r 0).toReal := by
    intro r hr x
    refine (hT4 r (lt_of_lt_of_le one_pos hr) x).trans ?_
    have hmono : M.case3Driver c r ≤ M.case3Driver c' r := M.case3Driver_mono hTri hc'c hr
    have hχnn : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hmono hχnn, hCp]
  have hdrv' : Tendsto (M.case3Driver c') atTop (𝓝 0) :=
    (Analysis.isLogErrorFunction_nablaTail_add_rpow_neg M hTail hc').2
  obtain ⟨c₀, hc₀, hχall⟩ := I418C.ChiInput.exists_chi_lower_uniform_and_finite M hβ hP
  have hχev : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (hχall r hr).2
  have hrate := M.eventually_sum_polyK_three_ballF_le_rate (δ := 1 / 2)
    (by norm_num) (by norm_num) hχev hTri
  refine ⟨3 * (C3 / c₃) + (C4 * Cp / c₃) + 1, c', ?_, hc', hc'2, hdrv', ?_⟩
  · have h1 : 0 ≤ C3 / c₃ := div_nonneg hC3 hc₃.le
    have h2' : 0 ≤ C4 * Cp / c₃ := div_nonneg (mul_nonneg hC4 hCp.le) hc₃.le
    linarith
  · filter_upwards [hrate, hgmr, eventually_ge_atTop (1 : ℝ)] with r hW hgmr' hr
    have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
    have hb : ((M.ball r).ncard : ℝ) ≠ 0 := by
      have := M.ball_ncard_pos r hr0
      positivity
    have hW3 : (∑ y ∈ E1Sign.ballF M r, I418C.polyK (M.cutTwoPoint r) 3 0 y)
        ≤ ((M.ball r).ncard : ℝ)
          * ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf
              + (M.nablaTail (Real.sqrt r)).toReal) := by
      refine hW.trans (le_of_eq ?_)
      norm_num
    have hstep := M.p2ExclError_le_of_windowed_ell_three (c := c') (Cp := Cp) (C3 := C3)
      (C4 := C4) (c₃ := c₃)
      (W := ((M.ball r).ncard : ℝ)
        * ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf + (M.nablaTail (Real.sqrt r)).toReal))
      (r := r) hCp.le hC3 hC4 hc₃ hr (h2 r hr) (hcM r hr) (hgapr r hr) hW3 (hT4' r hr) hgmr'
    rw [mul_div_cancel_left₀
      ((3 * r ^ (-(M.d : ℝ) / 2)) * M.triSelf + (M.nablaTail (Real.sqrt r)).toReal) hb] at hstep
    have htri : (0 : ℝ) ≤ M.triSelf := M.triPoint_nonneg 0 0
    have h1 : (0 : ℝ) ≤ 3 * r ^ (-(M.d : ℝ) / 2) * M.triSelf :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hr0 _)) htri
    have h2' : (0 : ℝ) ≤ (M.nablaTail (Real.sqrt r)).toReal := M.nablaTail_toReal_nonneg _
    have h3 : (0 : ℝ) ≤ M.case3Driver c' r := M.case3Driver_nonneg_of_one_le hr
    have hC3' : (0 : ℝ) ≤ C3 / c₃ := div_nonneg hC3 hc₃.le
    have hC4' : (0 : ℝ) ≤ C4 * Cp / c₃ := div_nonneg (mul_nonneg hC4 hCp.le) hc₃.le
    have hCtot : (0 : ℝ) ≤ 3 * (C3 / c₃) + (C4 * Cp / c₃) + 1 := by linarith
    nlinarith [hstep, h1, h2', h3, hC3', hC4', hCtot,
      mul_nonneg hC3' (add_nonneg h1 h2'), mul_nonneg hC4' h3]

/-- **The repaired Case-3 error is logarithmically integrable**, again with every constant
existential.  Adds only measurability of `r ↦ E_{2,r}` (the production `hmeasE2` obligation). -/
theorem exists_case3_error_logIntegrable
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hTail : Analysis.IsLogErrorFunction (fun r : ℝ => (M.nablaTail r).toReal))
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hcM : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgm : ∃ c₃ : ℝ, 0 < c₃ ∧
      ∀ᶠ r : ℝ in atTop, c₃ * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal)
    (hgap : ∃ C3 C4 : ℝ, 0 ≤ C3 ∧ 0 ≤ C4 ∧ ∀ r : ℝ, 1 ≤ r →
      ∀ y ∈ E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal
        ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * (M.cutMassAt r 0).toReal ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * (M.cutMassAt r 0).toReal ^ 3)
    (hmeasE2 : Measurable M.p2ExclError) :
    ∃ c : ℝ, 0 < c ∧ Analysis.LogarithmicallyIntegrable (M.case3Driver c) ∧
      Analysis.LogarithmicallyIntegrable M.p2ExclError := by
  obtain ⟨c₃, hc₃, hgmr⟩ := hgm
  obtain ⟨C3, C4, hC3, hC4, hgapr⟩ := hgap
  obtain ⟨c, Cp, hc, hCp, hT4⟩ := M.exists_polygonBound_four hP hTri
  set c' : ℝ := min c (1 / 2) with hc'_def
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc'2 : c' ≤ 1 / 2 := min_le_right _ _
  have hc'c : c' ≤ c := min_le_left _ _
  have hlogdrv : Analysis.LogarithmicallyIntegrable (M.case3Driver c') :=
    (Analysis.isLogErrorFunction_nablaTail_add_rpow_neg M hTail hc').1
  have hmeasNab : Measurable (fun r : ℝ => (M.nablaTail r).toReal) := hTail.1.1
  have hT4' : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 0 x ≤ Cp * M.case3Driver c' r * (M.cutMassAt r 0).toReal := by
    intro r hr x
    refine (hT4 r (lt_of_lt_of_le one_pos hr) x).trans ?_
    have hmono : M.case3Driver c r ≤ M.case3Driver c' r := M.case3Driver_mono hTri hc'c hr
    have hχnn : (0 : ℝ) ≤ (M.cutMassAt r 0).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hmono hχnn, hCp]
  exact ⟨c', hc', hlogdrv,
    M.logIntegrable_p2ExclError_of_windowed_ell_three hβ hP hTri hc' hc'2 hCp.le hC3 hC4 hc₃ h2
      hcM hgapr hT4' hgmr hlogdrv hmeasE2 hmeasNab⟩

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! # Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_polyK_three_ballF_le_two_scale
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_sum_polyK_three_ballF_le_rate
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeMass_toReal_le_of_windowed_ell_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_le_of_windowed_ell_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_windowed_ell_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_forall_polyK_three_le_case3Driver_of_tendsto
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_exists_case3_bundle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_repaired_case3_bundle
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.p2ExclError_tendsto_zero_of_case3_windowed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logIntegrable_p2ExclError_of_case3_windowed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_div_two_of_case3_windowed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_case3_error_rate
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_case3_error_logIntegrable
