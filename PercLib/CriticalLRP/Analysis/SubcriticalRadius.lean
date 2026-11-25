/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Existence of the subcritical radius from the sharpness asymptotic

Proposition I.4.2 chooses `r0(β)` from the assertion that the cutoff expected
cluster size is `o(r^α)`.  This file proves only that final asymptotic-to-threshold
step, with the sharpness estimate as an explicit input.
-/
module

public import PercLib.CriticalLRP.Analysis.ErrorFunctions

set_option autoImplicit false

@[expose] public section

open Filter
open scoped Topology Asymptotics

namespace PercLib.CriticalLRP.Analysis

/-- If `E(r) = o(r^α)`, there is a finite real radius above which
`E(r) ≤ (2α/β) r^α`.  This is exactly the threshold-existence step `i.4.g6`;
it neither proves `E(r) = o(r^α)` nor chooses a uniform radius as `β` varies. -/
theorem exists_radius_of_isLittleO_rpow {E : ℝ → ℝ} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hsharp : E =o[atTop] (fun r : ℝ => r ^ α)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, r₀ ≤ r → E r ≤ (2 * α / β) * r ^ α := by
  have hne : ∀ᶠ r : ℝ in atTop, r ^ α = 0 → E r = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    intro hz
    exact ((Real.rpow_pos_of_pos hr α).ne' hz).elim
  have hdiv : Tendsto (fun r : ℝ => E r / r ^ α) atTop (𝓝 0) :=
    (Asymptotics.isLittleO_iff_tendsto' hne).mp hsharp
  have hc : 0 < 2 * α / β := div_pos (mul_pos two_pos hα) hβ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdiv (2 * α / β) hc
  refine ⟨max N 1, lt_of_lt_of_le zero_lt_one (le_max_right N 1), ?_⟩
  intro r hr
  have hrN : N ≤ r := (le_max_left N 1).trans hr
  have hr1 : 1 ≤ r := (le_max_right N 1).trans hr
  have hrpos : 0 < r := zero_lt_one.trans_le hr1
  have habs : |E r / r ^ α| < 2 * α / β := by
    have h := hN r hrN
    rwa [Real.dist_eq, sub_zero] at h
  have hlt : E r / r ^ α < 2 * α / β := (le_abs_self _).trans_lt habs
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hrpos α)).mp hlt).le

/-- Trivial non-vacuity check: the identically-zero function satisfies the
input asymptotic and the threshold can be used at zero as well. -/
example : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, r₀ ≤ r →
    (fun _ : ℝ => (0 : ℝ)) r ≤ (2 * (1 : ℝ) / 1) * r ^ (1 : ℝ) := by
  apply exists_radius_of_isLittleO_rpow one_pos one_pos
  simp

#print axioms PercLib.CriticalLRP.Analysis.exists_radius_of_isLittleO_rpow

end PercLib.CriticalLRP.Analysis
