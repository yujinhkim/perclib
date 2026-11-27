/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

Ultramath swarm `smwziumdb`, member `m2`, direction `d5`.

# The far-region repair: its threshold is forced, exactly

A far-region repair keeps the two-term star display only outside a ball (`HasFarStar`).  This file
proves that the boundary cannot be anywhere it likes: at every vertex `y` where the display holds,
the two-point function is bounded by

  `T(0,y) ≤ (C₃ + C₄) ∇ / (c χ)`,

so the excluded region must contain every vertex with `T(0,y)` above that threshold.  The inputs
are the accepted `QZeroDiagInputs` (`c χ⁵ ≤ E|K|³`) and the Harris/FKG lower bound

  `T(0,y) · E|K_0|³ ≤ E[|K_0|³ 1(y ∈ K_0)]`

which is the integrated production theorem `QZeroRepair.Harris.harris_cutMoment` (proved from
`edgeMeasure_fkg_measurable_ennreal` by the labelled expansion); it is used, not re-proved.

Consequence: the "delete `y = 0`" repair and every repair that deletes only a fixed neighbourhood
are impossible in the Case-3 regime (`χ → ∞`), because `T(0,1)` is bounded below independently of
`r`: the far region must be defined by smallness of the two-point function, i.e. by an
`r`-dependent threshold.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Sharp
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepair.Harris

/-! # Independently reviewed Case-3 repair-audit module: Far -/


noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP
namespace QZeroRepairAudit

attribute [local instance] Classical.propDecidable

open Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The far-region threshold is forced.**  If the two-term star display holds at the vertex `y`
(of the far region), the Case-3 third-moment lower bound holds, and Harris/FKG bounds the star from
below by `T(0,y)` times the third moment, then

  `T(0,y) ≤ (C₃ + C₄) ∇ / (c χ)`.

Hence the excluded region of any far-region repair must contain
`{y : T(0,y) > (C₃+C₄) ∇ / (c χ)}`. -/
theorem far_threshold_necessary {c R : ℝ} (hQI : QZeroDiagInputs M c R) {C3 C4 : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    {r ρ : ℝ} (hr : max R 1 ≤ r) {y : M.V} (hfar : HasFarStar M C3 C4 ρ)
    (hy : ρ < M.S.dist 0 y) :
    M.cutTwoPoint r (0 : M.V) y ≤ (C3 + C4) * M.triSelf / (c * M.chiReal r) := by
  have h3 := hQI.third_lower r hr
  have hχ1 := hQI.chi_one_le r hr
  have hχ5pos : (0 : ℝ) < M.chiReal r ^ 5 := by
    have h1 : (0 : ℝ) < M.chiReal r := lt_of_lt_of_le one_pos hχ1
    positivity
  have h3ne : M.cutMoment 3 r ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h3
    have hpos : (0 : ℝ) < c * M.chiReal r ^ 5 := mul_pos hQI.c_pos hχ5pos
    linarith
  have hHarris := PercLib.CriticalLRP.Smwzg77c3.M7.harris_cutMoment M r h3ne y
  have hχfin : M.cutMassAt r 0 ≠ ⊤ := by
    intro htop
    have hzero : M.chiReal r = 0 := by
      simp only [SourceModelData.chiReal, htop, ENNReal.toReal_top]
    linarith
  have hP3 : I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ M.triSelf :=
    (hQI.powerInputs r hr).triSup y
  have hP4 : I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y ≤ M.triSelf * M.chiReal r :=
    (M.source_polyK_le_diag r hχfin 4 y).trans (polyK_four_diag_le M hQI hr)
  have hχ0 : (0 : ℝ) ≤ M.chiReal r := ENNReal.toReal_nonneg
  have hχ3 : (0 : ℝ) ≤ M.chiReal r ^ 3 := pow_nonneg hχ0 3
  have hχ4 : (0 : ℝ) ≤ M.chiReal r ^ 4 := pow_nonneg hχ0 4
  have hcp : (0 : ℝ) < c := hQI.c_pos
  have hinst := hfar r (le_trans (le_max_right R 1) hr) y hy
  have hH := hHarris
  -- `T · c χ⁵ ≤ T · E|K|³ ≤ star ≤ (C₃+C₄) ∇ χ⁴`
  have hTnn : (0 : ℝ) ≤ M.cutTwoPoint r (0 : M.V) y := M.cutTwoPoint_nonneg r 0 y
  have hstep : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3
      ≤ (C3 + C4) * M.triSelf * M.chiReal r ^ 4 := by
    have h1 : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4
        ≤ C3 * M.triSelf * M.chiReal r ^ 4 := by
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP3 hC3) hχ4
      linarith [h]
    have h2 : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3
        ≤ C4 * M.triSelf * M.chiReal r ^ 4 := by
      have h4 := mul_le_mul_of_nonneg_left hP4 hC4
      calc C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3
          ≤ C4 * (M.triSelf * M.chiReal r) * M.chiReal r ^ 3 :=
            mul_le_mul_of_nonneg_right h4 hχ3
        _ = C4 * M.triSelf * M.chiReal r ^ 4 := by ring
    linarith [h1, h2]
  have hkey : M.cutTwoPoint r (0 : M.V) y * (c * M.chiReal r ^ 5)
      ≤ (C3 + C4) * M.triSelf * M.chiReal r ^ 4 := by
    have h1 : M.cutTwoPoint r (0 : M.V) y * (c * M.chiReal r ^ 5)
        ≤ M.cutTwoPoint r (0 : M.V) y * (M.cutMoment 3 r).toReal :=
      mul_le_mul_of_nonneg_left h3 hTnn
    have h2 : M.cutTwoPoint r (0 : M.V) y * (M.cutMoment 3 r).toReal
        ≤ (M.connCubeVertexMass r y).toReal := hH
    have h3' : (M.connCubeVertexMass r y).toReal
        ≤ (C3 + C4) * M.triSelf * M.chiReal r ^ 4 := by
      calc (M.connCubeVertexMass r y).toReal
          ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
              C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3 := hinst
        _ ≤ (C3 + C4) * M.triSelf * M.chiReal r ^ 4 := hstep
    linarith [h1, h2, h3']
  -- divide by `χ⁴` and then by `c χ`
  have hχ1pos : (0 : ℝ) < M.chiReal r := lt_of_lt_of_le one_pos hχ1
  have hχ4pos : (0 : ℝ) < M.chiReal r ^ 4 := by positivity
  have hden : (0 : ℝ) < c * M.chiReal r := mul_pos hcp hχ1pos
  have hkey' : (M.cutTwoPoint r (0 : M.V) y * (c * M.chiReal r)) * M.chiReal r ^ 4
      ≤ ((C3 + C4) * M.triSelf) * M.chiReal r ^ 4 := by
    calc (M.cutTwoPoint r (0 : M.V) y * (c * M.chiReal r)) * M.chiReal r ^ 4
        = M.cutTwoPoint r (0 : M.V) y * (c * M.chiReal r ^ 5) := by ring
      _ ≤ (C3 + C4) * M.triSelf * M.chiReal r ^ 4 := hkey
      _ = ((C3 + C4) * M.triSelf) * M.chiReal r ^ 4 := by ring
  have hkey2 : M.cutTwoPoint r (0 : M.V) y * (c * M.chiReal r) ≤ (C3 + C4) * M.triSelf :=
    le_of_mul_le_mul_right hkey' hχ4pos
  exact (le_div_iff₀ hden).mpr hkey2


/-- **No fixed-radius far-region repair can work.**

If a vertex `y` outside the fixed ball `{z : ‖z‖ ≤ ρ}` has its two-point function bounded below by
a positive constant `t` (as every fixed near neighbour does, `T(0,1) ≍ β_c J(0,1)`), then the
far-region repair `HasFarStar M C₃ C₄ ρ` is **false**: `χ → ∞` drives the forced threshold
`(C₃+C₄)∇/(cχ)` below `t`.  So the excluded region has to be cut by smallness of `T(0,y)`, i.e. by
an `r`-dependent threshold; "delete `y = 0`" and "delete a fixed neighbourhood" both fail. -/
theorem not_hasFarStar_const {c R : ℝ} (hQI : QZeroDiagInputs M c R) {C3 C4 ρ t : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    {y : M.V} (hy : ρ < M.S.dist 0 y) (ht : 0 < t)
    (hT : ∀ r : ℝ, 1 ≤ r → t ≤ M.cutTwoPoint r (0 : M.V) y) :
    ¬ HasFarStar M C3 C4 ρ := by
  intro hfar
  have hct : (0 : ℝ) < c * t := mul_pos hQI.c_pos ht
  obtain ⟨r, hr, hbig⟩ :=
    hQI.chi_unbounded (max 1 ((C3 + C4) * M.triSelf / (c * t) + 1))
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_right R 1) hr
  have hχ1 := hQI.chi_one_le r hr
  have hχpos : (0 : ℝ) < M.chiReal r := lt_of_lt_of_le one_pos hχ1
  have hcχ : (0 : ℝ) < c * M.chiReal r := mul_pos hQI.c_pos hχpos
  have hB : (C3 + C4) * M.triSelf / (c * t) + 1 ≤ M.chiReal r := le_trans (le_max_right _ _) hbig
  have hlt : (C3 + C4) * M.triSelf / (c * M.chiReal r) < t := by
    have hctne : c * t ≠ 0 := ne_of_gt hct
    have hident : ((C3 + C4) * M.triSelf / (c * t) + 1) * (c * t)
        = (C3 + C4) * M.triSelf + c * t := by
      have hcne : c ≠ 0 := ne_of_gt hQI.c_pos
      field_simp [hcne, hctne]
    have h2 : ((C3 + C4) * M.triSelf / (c * t) + 1) * (c * t)
        ≤ M.chiReal r * (c * t) := mul_le_mul_of_nonneg_right hB hct.le
    rw [hident] at h2
    have hX : (C3 + C4) * M.triSelf < t * (c * M.chiReal r) := by
      have h3 : M.chiReal r * (c * t) = t * (c * M.chiReal r) := by ring
      linarith [h2, hct, h3.le, h3.ge]
    exact (div_lt_iff₀ hcχ).mpr hX
  have hbound := far_threshold_necessary M hQI hC3 hC4 hr hfar hy
  have hTge := hT r hr1
  linarith [hbound, hlt, hTge]

end SourceModelData

end QZeroRepairAudit
end PercLib.CriticalLRP
