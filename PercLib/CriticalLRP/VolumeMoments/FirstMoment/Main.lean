/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Member m5, swarm smwg5u3az — direction E (HD first-moment asymptotics).

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Section I.4.1.

Capstone: with the a priori bound of Lemma I.4.9 in hand (produced by
`first_moment_bound_all_beta`), the error `𝓔_{1,r}` is `O(r^{3α−d})`, hence the
multiplicative error `Ē_{1,r} = 1 − (1−𝓔_{0,r})(1−𝓔_{1,r})` of the first-moment
ODE (I.4.6) tends to zero, and Proposition I.4.2's conclusion

  `E_{β_c,r}|K| ∼ (α/β_c) r^α`

together with logarithmic integrability of the error
`H_r = (β_c/α) r^{-α} E_{β_c,r}|K| − 1` follow from `first_moment_asymptotic`
and `first_moment_error_logIntegrable`.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.FirstMoment.Bootstrap

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace PercLib.CriticalLRP.VolumeMoments.FirstMoment

/-- The multiplicative error of (I.4.6) written in terms of `𝓔₀, 𝓔₁`:
`e = 1 − (1−𝓔₀)(1−𝓔₁) = 𝓔₀ + 𝓔₁(1−𝓔₀)`. -/
theorem error_decomp {E0 E1 : ℝ} (hE0 : |E0| ≤ 1 / 8) (hE1 : 0 ≤ E1) :
    |1 - (1 - E0) * (1 - E1)| ≤ |E0| + (9 / 8) * E1 := by
  have h1 : |1 - E0| ≤ 9 / 8 := by
    have h := abs_le.1 hE0
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  have hkey : (1 - (1 - E0) * (1 - E1)) = E0 + E1 * (1 - E0) := by ring
  rw [hkey]
  have h3 : |E1 * (1 - E0)| ≤ (9 / 8) * E1 := by
    rw [abs_mul]
    calc |E1| * |1 - E0| ≤ E1 * (9 / 8) := by
          rw [abs_of_nonneg hE1]
          exact mul_le_mul_of_nonneg_left h1 hE1
      _ = (9 / 8) * E1 := by ring
  calc |E0 + E1 * (1 - E0)| ≤ |E0| + |E1 * (1 - E0)| := abs_add_le _ _
    _ ≤ |E0| + (9 / 8) * E1 := by linarith [h3]

/-- **Proposition I.4.2, Case 1 — conclusion.**

Given the first-moment ODE (I.4.6) at `β = β_c` with multiplicative error
`Ē = 1 − (1−𝓔₀)(1−𝓔₁)`, where `𝓔₀ → 0` satisfies `|𝓔₀| ≤ 1/8` and
`0 ≤ 𝓔₁ r ≤ c r^{3α−d}` (the bound furnished by Lemma I.4.7, the tree-graph
inequality and the a priori estimate of Lemma I.4.9), the first moment has the
mean-field asymptotic `E_{β_c,r}|K| ∼ (α/β_c) r^α`. -/
theorem first_moment_asymptotic_at_critical
    {F F' E0 E1 : ℝ → ℝ} {α βc d c r₀ : ℝ}
    (hα : 0 < α) (hβc : 0 < βc) (hγ : 0 < d - 3 * α) (hc : 0 ≤ c)
    (hr₀pos : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t → HasDerivAt F (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < F t)
    (hinf : Tendsto F atTop atTop)
    (hODE : ∀ t, r₀ ≤ t →
      F' t = (1 - (1 - (1 - E0 t) * (1 - E1 t))) * βc * t ^ (-α - 1) * (F t) ^ 2)
    (hE0 : Tendsto E0 atTop (𝓝 0)) (hE0b : ∀ t, r₀ ≤ t → |E0 t| ≤ 1 / 8)
    (hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t ∧ E1 t ≤ c * t ^ (3 * α - d))
    (hmeas : Measurable (fun t => 1 - (1 - E0 t) * (1 - E1 t))) :
    Tendsto (fun r => F r / (α / βc * r ^ α)) atTop (𝓝 1) := by
  set e : ℝ → ℝ := fun t => 1 - (1 - E0 t) * (1 - E1 t) with hedef
  -- `e → 0`
  have hE1tend : Tendsto E1 atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => c * t ^ (3 * α - d)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => c * t ^ (-(d - 3 * α))) atTop (𝓝 (c * 0)) :=
        (tendsto_rpow_neg_atTop (by linarith : 0 < d - 3 * α)).const_mul c
      have h0' : Tendsto (fun t : ℝ => c * t ^ (3 * α - d)) atTop (𝓝 (c * 0)) := by
        refine h0.congr' ?_
        filter_upwards with t
        rw [show -(d - 3 * α) = 3 * α - d by ring]
      simpa using h0'
    rw [Metric.tendsto_atTop] at h1 ⊢
    intro ε hε
    obtain ⟨T, hT⟩ := h1 ε hε
    refine ⟨max T r₀, fun t ht => ?_⟩
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htr : r₀ ≤ t := le_trans (le_max_right _ _) ht
    have hlt := hT t htT
    rw [Real.dist_eq, sub_zero] at hlt ⊢
    have hb : |E1 t| ≤ c * t ^ (3 * α - d) := by
      rw [abs_of_nonneg (hE1 t htr).1]
      exact (hE1 t htr).2
    have hpos : (0:ℝ) ≤ c * t ^ (3 * α - d) := by
      apply mul_nonneg hc
      exact Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hr₀pos htr)) _
    have hlt' : c * t ^ (3 * α - d) < ε := by
      rw [abs_of_nonneg hpos] at hlt
      exact hlt
    exact lt_of_le_of_lt hb hlt'

  have he0 : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => (1 - E0 t) * (1 - E1 t)) atTop (𝓝 ((1 - 0) * (1 - 0))) :=
      (tendsto_const_nhds.sub hE0).mul (tendsto_const_nhds.sub hE1tend)
    have h2 : Tendsto (fun t : ℝ => 1 - (1 - E0 t) * (1 - E1 t)) atTop
        (𝓝 (1 - (1 - 0) * (1 - 0))) :=
      tendsto_const_nhds.sub h1
    simpa [hedef] using h2
  -- `|e|` is bounded on `[r₀,∞)`
  have hbnd : ∀ t, r₀ ≤ t → |e t| ≤ 1 / 8 + (9 / 8) * (c * r₀ ^ (3 * α - d)) := by
    intro t ht
    have h1 := error_decomp (hE0b t ht) (hE1 t ht).1
    have h2 : E1 t ≤ c * r₀ ^ (3 * α - d) := by
      have h3 : t ^ (3 * α - d) ≤ r₀ ^ (3 * α - d) :=
        Real.rpow_le_rpow_of_nonpos hr₀pos ht (by linarith)
      have h4 : 0 ≤ c := hc
      nlinarith [(hE1 t ht).2, h3, h4, Real.rpow_pos_of_pos hr₀pos (3 * α - d)]
    calc |e t| ≤ |E0 t| + (9 / 8) * E1 t := h1
      _ ≤ 1 / 8 + (9 / 8) * (c * r₀ ^ (3 * α - d)) := by
          have h5 : (9 / 8) * E1 t ≤ (9 / 8) * (c * r₀ ^ (3 * α - d)) := by nlinarith
          linarith [hE0b t ht, h5]
  exact first_moment_asymptotic hβc hα hr₀pos hderiv hpos hinf
    (fun t ht => by rw [hODE t ht]; simp only [hedef]; ring) hmeas
    (fun t ht => hbnd t ht) he0

end PercLib.CriticalLRP.VolumeMoments.FirstMoment
