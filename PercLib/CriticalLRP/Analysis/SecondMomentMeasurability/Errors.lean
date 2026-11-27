/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Measurability of the second-moment error functions `𝓔_{2,r}`, `𝓗_r`, `Ē_{2,r}`

Swarm `smwyvlg99`, member `m2`, direction `d2`.

`SecondMomentCase1` and `SecondMomentCase3` carry three further measurability hypotheses of the
same family as `hmR`:

`hmeasE2 : Measurable M.p2ExclError`,  `hmeasEbar : Measurable M.p2Ebar`,
`hmeas : Measurable M.p2ExclError`.

They are discharged here, from

* `(∀ r, M.cutMoment 1 r ≠ ⊤)` and `(∀ r, M.cutMoment 2 r ≠ ⊤)` — the cutoff moments whose real
  shadows appear in the definitions (`measurable_cutMoment_toReal`);
* `h4 : ∀ x > 0, ∃ r₁ > x, M.cutMoment 4 r₁ ≠ ⊤` — used only through the landed **right**
  continuity of the two monotone marked window masses `quadPairMass` and `connCubeMass`, whose
  difference is `exclMassQuad` on a right-neighbourhood of each positive radius.

The three definitions are the paper's own algebraic combinations
(`VolumeMoments.cE2`, `VolumeMoments.oneSubEbar2`, `VolumeMoments.oneSubE0`), so their measurability
is closure of `Measurable` under the displayed arithmetic once the four inputs
`r ↦ (cutMoment 1 r)ᵗᵒᴿᵉᵃˡ`, `r ↦ (cutMoment 2 r)ᵗᵒᴿᵉᵃˡ`, `r ↦ (exclMassQuad r)ᵗᵒᴿᵉᵃˡ`,
`r ↦ |B_r|` and `r ↦ |K'(r)|` are measurable.  Note `r ↦ (M.ball r).ncard` is measurable with no
hypothesis at all, being monotone.

No `hac`, no `hae`, no continuity at an attained radius, no left limit.

No `sorry`, `admit`, `native_decide` or custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentMeasurability.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentError.Normalized

/-! # Measurability of second-moment errors -/

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

/-! ## 1. The window cardinality and the excluded quadratic mass -/

/-- The lattice ball is monotone in the radius. -/
theorem ball_mono {r r' : ℝ} (hrr' : r ≤ r') : M.ball r ⊆ M.ball r' :=
  fun _ hy => le_trans hy hrr'

/-- **`r ↦ |B_r|` is measurable**, unconditionally: it is monotone. -/
theorem measurable_ball_ncard : Measurable fun r : ℝ => ((M.ball r).ncard : ℝ) := by
  have hmono : Monotone fun r : ℝ => ((M.ball r).ncard : ℝ) := by
    intro r r' hrr'
    have h := Set.ncard_le_ncard (M.ball_mono hrr') (M.finite_ball r')
    exact Nat.cast_le.mpr h
  exact hmono.measurable

/-- **`r ↦ (M.exclMassQuad r)ᵗᵒᴿᵉᵃˡ` is measurable.**

`exclMassQuad = quadPairMass - connCubeMass` (`quadPairMass_eq_connCube_add`), both monotone marked
window masses are right continuous by the landed statements, and at `r ≤ 0` the excluded window is
empty. -/
theorem measurable_exclMassQuad_toReal
    (h4 : ∀ x : ℝ, 0 < x → ∃ r1 : ℝ, x < r1 ∧ M.cutMoment 4 r1 ≠ ⊤) :
    Measurable fun r : ℝ => (M.exclMassQuad r).toReal := by
  refine measurable_of_tendsto_nhdsGT (s := Set.Ioi 0) measurableSet_Ioi ?_ ?_
  · intro x hx
    obtain ⟨r1, hr1, h4r1⟩ := h4 x hx
    have hA := M.tendsto_quadPairMass_toReal_nhdsGT x hx hr1 h4r1
    have hC := M.tendsto_connCubeMass_toReal_nhdsGT x hx hr1 h4r1
    have hlim : Tendsto
        (fun r => (M.quadPairMass r).toReal - (M.connCubeMass r).toReal) (𝓝[>] x)
        (𝓝 ((M.quadPairMass x).toReal - (M.connCubeMass x).toReal)) := hA.sub hC
    have hev : (fun r => (M.exclMassQuad r).toReal) =ᶠ[𝓝[>] x]
        fun r => (M.quadPairMass r).toReal - (M.connCubeMass r).toReal := by
      filter_upwards [Ioo_mem_nhdsGT hr1] with r hr
      have h4r : M.cutMoment 4 r ≠ ⊤ := M.cutMoment_ne_top_of_le (le_of_lt hr.2) 4 h4r1
      have hAne := M.quadPairMass_ne_top h4r
      have hCne := M.connCubeMass_ne_top h4r
      have hEne : M.exclMassQuad r ≠ ⊤ := by
        refine ne_top_of_le_ne_top (M.p2RHS_ne_top_of_fourth h4r) ?_
        rw [SourceModelData.p2RHS]
        exact le_self_add
      have h1 := congrArg ENNReal.toReal (M.quadPairMass_eq_connCube_add r)
      rw [ENNReal.toReal_add hCne hEne] at h1
      linarith
    have h4x : M.cutMoment 4 x ≠ ⊤ := M.cutMoment_ne_top_of_le (le_of_lt hr1) 4 h4r1
    have hAx := M.quadPairMass_ne_top h4x
    have hCx := M.connCubeMass_ne_top h4x
    have hEx : M.exclMassQuad x ≠ ⊤ := by
      refine ne_top_of_le_ne_top (M.p2RHS_ne_top_of_fourth h4x) ?_
      rw [SourceModelData.p2RHS]
      exact le_self_add
    have hval : (M.quadPairMass x).toReal - (M.connCubeMass x).toReal
        = (M.exclMassQuad x).toReal := by
      have h1 := congrArg ENNReal.toReal (M.quadPairMass_eq_connCube_add x)
      rw [ENNReal.toReal_add hCx hEx] at h1
      linarith
    rw [hval] at hlim
    exact (tendsto_congr' hev).mpr hlim
  · intro x hx
    simp only [Set.mem_Ioi, not_lt] at hx
    simp [SourceModelData.exclMassQuad, M.exclSumQuad_eq_zero_of_nonpos hx]

/-! ## 2. The three error functions -/

/-- **`M.p2ExclError` is measurable.** -/
theorem measurable_p2ExclError (h1 : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤)
    (h2 : ∀ r : ℝ, M.cutMoment 2 r ≠ ⊤)
    (h4 : ∀ x : ℝ, 0 < x → ∃ r1 : ℝ, x < r1 ∧ M.cutMoment 4 r1 ≠ ⊤) :
    Measurable M.p2ExclError := by
  have hA : Measurable fun r : ℝ => (M.cutMoment 1 r).toReal :=
    M.measurable_cutMoment_toReal 1 h1
  have hA2 : Measurable fun r : ℝ => (M.cutMoment 2 r).toReal :=
    M.measurable_cutMoment_toReal 2 h2
  have hU : Measurable fun r : ℝ => (M.exclMassQuad r).toReal :=
    M.measurable_exclMassQuad_toReal h4
  have hb : Measurable fun r : ℝ => ((M.ball r).ncard : ℝ) := M.measurable_ball_ncard
  have hP : Measurable fun r : ℝ =>
      ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal :=
    (hb.mul hA).mul hA2
  have hfun : M.p2ExclError = fun r : ℝ =>
      (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal
        - (M.exclMassQuad r).toReal)
      / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal) := by
    funext r
    simp only [SourceModelData.p2ExclError, VolumeMoments.cE2]
  rw [hfun]
  exact hP.sub hU |>.div hP

/-- **`M.p2H` is measurable** from measurability of the first cutoff moment alone. -/
theorem measurable_p2H (hα : 0 < M.α) (h1 : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤) :
    Measurable M.p2H := by
  have hA : Measurable fun r : ℝ => (M.cutMoment 1 r).toReal :=
    M.measurable_cutMoment_toReal 1 h1
  have hden : Measurable fun r : ℝ => M.α / (M.betaCrit : ℝ) * r ^ M.α :=
    measurable_const.mul (Real.continuous_rpow_const (q := M.α)).measurable
  have hfun : M.p2H = fun r : ℝ =>
      (M.cutMoment 1 r).toReal / (M.α / (M.betaCrit : ℝ) * r ^ M.α) - 1 := by
    funext r
    simp only [SourceModelData.p2H]
  rw [hfun]
  exact (hA.div hden).sub measurable_const

/-- **`M.p2Ebar` is measurable** from the measurabilities of `𝓔_{2,r}`, `𝓗_r` and the cutoff
moments, with the kernel coefficient entering only through the unconditional measurability of
`deriv M.K`. -/
theorem measurable_p2Ebar (hα : 0 < M.α) (h1 : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤)
    (h2 : ∀ r : ℝ, M.cutMoment 2 r ≠ ⊤)
    (h4 : ∀ x : ℝ, 0 < x → ∃ r1 : ℝ, x < r1 ∧ M.cutMoment 4 r1 ≠ ⊤) :
    Measurable M.p2Ebar := by
  have hE2 : Measurable M.p2ExclError := M.measurable_p2ExclError h1 h2 h4
  have hH : Measurable M.p2H := M.measurable_p2H hα h1
  have hJ : Measurable fun r : ℝ => |deriv M.K r| := (measurable_deriv M.K).abs
  have hb : Measurable fun r : ℝ => ((M.ball r).ncard : ℝ) := M.measurable_ball_ncard
  have hpow : Measurable fun r : ℝ => r ^ (M.α + 1) :=
    (Real.continuous_rpow_const (q := M.α + 1)).measurable
  have hfun : M.p2Ebar = fun r : ℝ =>
      1 - ((1 - M.p2ExclError r) * (1 + M.p2H r)
        * (|deriv M.K r| * ((M.ball r).ncard : ℝ) * r ^ (M.α + 1))) := by
    funext r
    simp only [SourceModelData.p2Ebar, VolumeMoments.oneSubEbar2, VolumeMoments.oneSubE0]
  rw [hfun]
  exact measurable_const.sub (((measurable_const.sub hE2).mul (measurable_const.add hH)).mul
    ((hJ.mul hb).mul hpow))

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_ball_ncard
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_exclMassQuad_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_p2ExclError
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_p2H
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_p2Ebar
