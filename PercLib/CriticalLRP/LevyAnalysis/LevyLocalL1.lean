/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I: High effective
dimension", arXiv:2508.18807v1, Section I.5.2.

The paper states, after (I.5.16), that the truncated densities converge to the `α`-stable density
"in both `L∞` and local `L¹`". The `L∞` statement is `levyDens_gap_tendsto_uniform`
(`LevyGap.lean`). Here we prove the local `L¹` statement: for every radius `R`, the `L¹` distance
between the densities on `B_R` tends to `0` as `lam → ∞`.

The bound is uniform in `R`: `∫_{B_R} (dΠ_∞/dx - dΠ_lam/dx) ≤ lam^{-α} |B_1|`, because the gap is
`α/(d+α) min (‖x‖^{-d-α}) (lam^{-d-α})` and the mass of that minimum over *all* of `ℝ^d` is
`((d+α)/α) lam^{-α} |B_1|` (`lintegral_min_rpow`).
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.Measures
public import PercLib.CriticalLRP.LevyAnalysis.LevyGap
public import PercLib.CriticalLRP.LevyAnalysis.LevyMass

set_option autoImplicit true

@[expose] public section

open MeasureTheory Metric Set Filter
open Module
open scoped ENNReal NNReal Topology Pointwise Interval

namespace PercLib.CriticalLRP.LevyAnalysis

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The density gap integrated over a ball, dominated by `lam^{-α}|B_1|`, uniformly in the radius. -/
theorem lintegral_gap_ball_le (μ : Measure E) [μ.IsAddHaarMeasure] {α r : ℝ} (hα : 0 < α)
    (hr : 0 < r) (R : ℝ) :
    ∫⁻ x in ball (0 : E) R, (levyDensInf (E := E) α x - levyDensLam (E := E) α r x) ∂μ
      ≤ ENNReal.ofReal (r ^ (-α)) * μ (ball (0 : E) 1) := by
  calc ∫⁻ x in ball (0 : E) R, (levyDensInf (E := E) α x - levyDensLam (E := E) α r x) ∂μ
      ≤ ∫⁻ x, (levyDensInf (E := E) α x - levyDensLam (E := E) α r x) ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (r ^ (-α)) * μ (ball (0 : E) 1) := lintegral_levyDens_gap μ hα hr

/-- **Local `L¹` convergence of the truncated densities**: for every `R`,
`∫_{B_R} (dΠ_lam/dx - dΠ_∞/dx) → 0` as `lam → ∞` (in real-valued form). -/
theorem tendsto_toReal_lintegral_gap_ball (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (R : ℝ) :
    Tendsto (fun r : ℝ => (∫⁻ x in ball (0 : E) R,
        (levyDensInf (E := E) α x - levyDensLam (E := E) α r x) ∂μ).toReal) atTop (𝓝 0) := by
  have hmass : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hupper : Tendsto (fun r : ℝ => r ^ (-α) * (μ (ball (0 : E) 1)).toReal) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => r ^ (-α)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := α) hα
      simpa using this
    simpa using h.mul_const _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun r => ENNReal.toReal_nonneg) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hb := lintegral_gap_ball_le μ hα hr R
  calc (∫⁻ x in ball (0 : E) R,
        (levyDensInf (E := E) α x - levyDensLam (E := E) α r x) ∂μ).toReal
      ≤ (ENNReal.ofReal (r ^ (-α)) * μ (ball (0 : E) 1)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmass) hb
    _ = r ^ (-α) * (μ (ball (0 : E) 1)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _)]

end PercLib.CriticalLRP.LevyAnalysis
