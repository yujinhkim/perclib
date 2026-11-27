/-
Accepted from Ultramath `smwzg77c3`, member `m7`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d6`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The source's first-moment asymptotic makes the susceptibility unbounded

`Main.lean` refutes the uniform two-term estimate under the hypothesis that `3 * chi` is unbounded
along the radii.  That hypothesis is not an extra assumption: it is a consequence of the model's
first-moment asymptotic `hP` (the source input used throughout the Case-3 chain),

    chi_r / ((alpha / beta_c) * r^alpha) -> 1,

together with `alpha > 0`, `beta_c > 0`.  This file derives it, so that the refutations
`not_starTwoTermBound_of_hP` / `not_starTwoTermBoundWindow_of_hP` depend only on

* `hP` and `hTri` (the model's own Case-3 inputs),
* the growth `3 * chi^5 <= E|K_0|^3` (the `p = 3` case of Proposition I.4.20 together with the
  Case-3 relation `E|K|^2 >~ (E|K|)^3`; see `growth_of_higherMoment`).
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepair.Main

/-! # Unboundedness of the finite-cutoff susceptibility -/

noncomputable section

open Filter MeasureTheory Measure
open scoped ENNReal NNReal Topology BigOperators

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.Smwzg77c3.M7

open PercLib.CriticalLRP Orchestration

variable (M : SourceModelData)

/-- **`chi` is unbounded along the radii** under the model's first-moment asymptotic. -/
theorem chi_unbounded
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hα : 0 < M.α) (hβ : 0 < M.betaCrit) :
    ∀ B : ℝ, ∃ r : ℝ, 1 ≤ r ∧ B < 3 * chi M r := by
  intro B
  set c : ℝ := M.α / (M.betaCrit : ℝ) with hcdef
  have hc : 0 < c := div_pos hα hβ
  have hrpow : Tendsto (fun r : ℝ => r ^ M.α) atTop atTop := tendsto_rpow_atTop hα
  have hhalf : ∀ᶠ r : ℝ in atTop,
      (1 / 2 : ℝ) ≤ (M.cutMassAt r 0).toReal / (c * r ^ M.α) := by
    have h : ∀ᶠ r : ℝ in atTop,
        (1 / 2 : ℝ) < (M.cutMassAt r 0).toReal / (c * r ^ M.α) := by
      have := hP.eventually (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
      simpa only [hcdef] using this
    filter_upwards [h] with r hr using le_of_lt hr
  have hbig : ∀ᶠ r : ℝ in atTop,
      (max 1 B + 1) / (3 * ((1 / 2) * c)) ≤ r ^ M.α :=
    tendsto_atTop.1 hrpow _
  have hall : ∀ᶠ r : ℝ in atTop,
      (1 / 2 : ℝ) ≤ (M.cutMassAt r 0).toReal / (c * r ^ M.α)
        ∧ (max 1 B + 1) / (3 * ((1 / 2) * c)) ≤ r ^ M.α ∧ 1 ≤ r :=
    hhalf.and (hbig.and (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨r, h1, h2, hr1⟩ := hall.exists
  refine ⟨r, hr1, ?_⟩
  have hrp : (0 : ℝ) < r ^ M.α := Real.rpow_pos_of_pos (by linarith) _
  have hcpos : (0 : ℝ) < c * r ^ M.α := mul_pos hc hrp
  have hχeq : chi M r = ((M.cutMassAt r 0).toReal / (c * r ^ M.α)) * (c * r ^ M.α) := by
    rw [chi, div_mul_cancel₀]
    exact ne_of_gt hcpos
  have hstep1 : (1 / 2) * (c * r ^ M.α) ≤ chi M r := by
    rw [hχeq]
    exact mul_le_mul_of_nonneg_right h1 (le_of_lt hcpos)
  have hstep2 : (1 / 2) * (c * ((max 1 B + 1) / (3 * ((1 / 2) * c))))
      ≤ (1 / 2) * (c * r ^ M.α) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact mul_le_mul_of_nonneg_left h2 (le_of_lt hc)
  have hval : (1 / 2) * (c * ((max 1 B + 1) / (3 * ((1 / 2) * c)))) = (max 1 B + 1) / 3 := by
    field_simp
  have h3 : (max 1 B + 1) / 3 ≤ chi M r := by
    linarith [hstep1, hstep2, hval]
  have h4 : B ≤ max 1 B := le_max_right _ _
  linarith [h3, h4]

/-- **The uniform two-term estimate fails** under the model's own Case-3 inputs. -/
theorem not_starTwoTermBound_of_hP {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hα : 0 < M.α) (hβ : 0 < M.betaCrit)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (hgrowth : ∀ r : ℝ, 1 ≤ r → 3 * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal) :
    ¬ StarTwoTermBound M C3 C4 :=
  not_starTwoTermBound M hC3 hC4 hTri hχ hgrowth (chi_unbounded M hP hα hβ)

/-- **The uniform window estimate fails** under the model's own Case-3 inputs. -/
theorem not_starTwoTermBoundWindow_of_hP {C3 C4 : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hα : 0 < M.α) (hβ : 0 < M.betaCrit)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (h0 : ∀ r : ℝ, 1 ≤ r → (0 : M.V) ∈ E1Sign.ballF M r)
    (hgrowth : ∀ r : ℝ, 1 ≤ r → 3 * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal) :
    ¬ StarTwoTermBoundWindow M C3 C4 :=
  not_starTwoTermBoundWindow M hC3 hC4 hTri hχ h0 hgrowth (chi_unbounded M hP hα hβ)

end PercLib.CriticalLRP.Smwzg77c3.M7

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.chi_unbounded
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.not_starTwoTermBound_of_hP
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.not_starTwoTermBoundWindow_of_hP
