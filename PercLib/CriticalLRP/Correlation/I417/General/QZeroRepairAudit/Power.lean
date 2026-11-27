/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

Ultramath swarm `smwziumdb`, member `m2`, direction `d5`.

# The exponent `χ⁵` is forced: no correction of order `T(0,y)^k χ^β`, `β < 5`, can repair the star

`Sharp.diag_correction_lower_bound` forces every correction term at the diagonal to be of order
`χ⁵`.  Here we turn that into the power statement: the repair

  `E[|K_0|³1(y∈K_0)] ≤ C₃ T³χ⁴ + C₄ T⁴χ³ + C₅ T(0,y)^k χ^β`

is impossible for every real `β < 5` and every `k : ℕ`.  At `y = 0` the left-hand side is
`⪰ c χ⁵` while the correction is `C₅ χ^β = o(χ⁵)`, and the two main terms are `o(χ⁵)` as well.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Sharp

/-! # Independently reviewed Case-3 repair-audit module: Power -/


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

/-- **No power correction with exponent `β < 5` repairs the star.** -/
theorem power_additive_impossible {c R : ℝ} (hQI : QZeroDiagInputs M c R) {C3 C4 C5 : ℝ}
    {k : ℕ} {β : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hβ : β < 5)
    (hadd : HasPowerAdditiveStar M C3 C4 C5 k β) : False := by
  have hcpos : (0 : ℝ) < c := hQI.c_pos
  have hε : (0 : ℝ) < c / 4 := by linarith
  -- the two main terms at the diagonal are `o(χ⁵)`
  have hβ5 : (0 : ℝ) < 5 - β := by linarith
  have htend : Tendsto (fun x : ℝ => C5 * x ^ (β - 5)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := 5 - β) hβ5
    have hexp : -(5 - β) = β - 5 := by ring
    rw [hexp] at h
    simpa using h.const_mul C5
  have hev : ∀ᶠ x : ℝ in atTop, C5 * x ^ (β - 5) ≤ c / 4 := by
    have hlt := (tendsto_order.1 htend).2 (c / 4) hε
    filter_upwards [hlt] with x hx using hx.le
  rw [eventually_atTop] at hev
  obtain ⟨B₁, hB₁⟩ := hev
  obtain ⟨r, hr, hbig⟩ :=
    hQI.chi_unbounded (max B₁ ((C3 + C4) * M.triSelf / (c / 4) + 1))
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_right R 1) hr
  have hχ1 := hQI.chi_one_le r hr
  have hχpos : (0 : ℝ) < M.chiReal r := lt_of_lt_of_le one_pos hχ1
  have hχB1 : B₁ ≤ M.chiReal r := le_trans (le_max_left _ _) hbig
  have hχB2 : (C3 + C4) * M.triSelf / (c / 4) + 1 ≤ M.chiReal r :=
    le_trans (le_max_right _ _) hbig
  have hpow : C5 * M.chiReal r ^ (β - 5) ≤ c / 4 := hB₁ _ hχB1
  have hx1 : (C3 + C4) * M.triSelf / M.chiReal r ≤ c / 4 :=
    div_le_of_le_div_add_one hε hχpos hχB2
  -- instantiate the repair at `y = 0`
  have hinst := hadd r hr1 0
  rw [M.cutTwoPoint_self_eq_one r (0 : M.V), one_pow] at hinst
  have hb := diag_correction_lower_bound M hQI hC3 hC4 hr hinst
  have hχ5 : (0 : ℝ) < M.chiReal r ^ 5 := by positivity
  have h4 : (C3 + C4) * M.triSelf * M.chiReal r ^ 4 ≤ (c / 4) * M.chiReal r ^ 5 := by
    have heq : (C3 + C4) * M.triSelf * M.chiReal r ^ 4
        = ((C3 + C4) * M.triSelf / M.chiReal r) * M.chiReal r ^ 5 := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right hx1 hχ5.le
  have h5 : C5 * M.chiReal r ^ β ≤ (c / 4) * M.chiReal r ^ 5 := by
    have heq : C5 * M.chiReal r ^ β
        = (C5 * M.chiReal r ^ (β - 5)) * M.chiReal r ^ 5 := by
      rw [show M.chiReal r ^ 5 = M.chiReal r ^ (5 : ℝ) from (Real.rpow_natCast _ 5).symm,
        mul_assoc, ← Real.rpow_add hχpos]
      congr 2
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hpow hχ5.le
  have hsum : c * M.chiReal r ^ 5 ≤ (c / 2) * M.chiReal r ^ 5 := by
    have hsplit : (c / 4) * M.chiReal r ^ 5 + (c / 4) * M.chiReal r ^ 5
        = (c / 2) * M.chiReal r ^ 5 := by ring
    linarith [hb, h4, h5, hsplit]
  have hcle : c ≤ c / 2 := le_of_mul_le_mul_right hsum hχ5
  linarith

end SourceModelData

end QZeroRepairAudit
end PercLib.CriticalLRP
