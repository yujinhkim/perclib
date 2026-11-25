/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I: High effective
dimension", arXiv:2508.18807v1, Section I.5.2.

This file proves the *mass* computation of Section I.5.2: the total mass of the density gap
`dΠ_∞/dx - dΠ_lam/dx`, which is the content of (I.5.18) (the case `lam = 1`: the extra-jump mass is
one under the normalisation `|B_1| = 1`), in the sharper form `Π_∞ - Π_lam` has mass `lam^{-α}|B_1|`.

The key analytic input is a layer-cake/Tonelli computation for the function
`x ↦ min (‖x‖^{-d-α}) (r^{-d-α})`, which avoids polar coordinates entirely: for `‖x‖ > 0`,
`min (‖x‖^{-d-α}) (r^{-d-α}) = (d+α) ∫_{max (r, ‖x‖)}^∞ s^{-d-α-1} ds`,
and the ball masses `|B_s| = s^d |B_1|` are supplied by `lintegral_ball_hom`.
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.Measures
public import PercLib.CriticalLRP.LevyAnalysis.LevyGap

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Metric Set Filter
open Module
open scoped ENNReal NNReal Topology Pointwise Interval

namespace PercLib.CriticalLRP.LevyAnalysis

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ## The one-dimensional building blocks -/

/-- `∫_{Ioi a} c s^q ds = c (-a^{q+1}/(q+1))` for `q < -1`, in `ℝ≥0∞`-integral form. -/
theorem lintegral_Ioi_const_mul_rpow {c q a : ℝ} (hc : 0 ≤ c) (hq : q < -1) (ha : 0 < a) :
    ∫⁻ s in Ioi a, ENNReal.ofReal (c * s ^ q)
      = ENNReal.ofReal (c * (-(a ^ (q + 1)) / (q + 1))) := by
  have hint : IntegrableOn (fun s : ℝ => c * s ^ q) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt hq ha).const_mul c
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a)] fun s : ℝ => c * s ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg hc (Real.rpow_nonneg (le_of_lt (lt_trans ha hs)) q)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_Ioi_rpow_of_lt hq ha]

/-- The layer integral of the weight `(d+α) s^{-d-α-1}` over `Ioi a`. -/
theorem lintegral_Ioi_levy_layer {α : ℝ} (hα : 0 < α) {a : ℝ} (ha : 0 < a) :
    ∫⁻ s in Ioi a, ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1))
      = ENNReal.ofReal (a ^ (-(finrank ℝ E : ℝ) - α)) := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hq : -(finrank ℝ E : ℝ) - α - 1 < -1 := by linarith
  have hle : (0 : ℝ) ≤ (finrank ℝ E : ℝ) + α := by linarith
  rw [lintegral_Ioi_const_mul_rpow hle hq ha]
  congr 1
  have hexp : -(finrank ℝ E : ℝ) - α - 1 + 1 = -(finrank ℝ E : ℝ) - α := by ring
  rw [hexp]
  have hne : (-(finrank ℝ E : ℝ) - α) ≠ 0 := by linarith
  field_simp
  ring

/-- The layer integral of the weight `(d+α) s^{-α-1}` over `Ioi r`. -/
theorem lintegral_Ioi_levy_tail {α : ℝ} (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    ∫⁻ s in Ioi r, ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-α - 1))
      = ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * r ^ (-α) / α) := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hq : -α - 1 < -1 := by linarith
  have hle : (0 : ℝ) ≤ (finrank ℝ E : ℝ) + α := by linarith
  rw [lintegral_Ioi_const_mul_rpow hle hq hr]
  congr 1
  have hexp : -α - 1 + 1 = -α := by ring
  rw [hexp]
  field_simp

/-- The ball mass `|B_s| = s^d |B_1|` of an additive Haar measure. -/
theorem measure_ball_eq_ofReal_mul (μ : Measure E) [μ.IsAddHaarMeasure] {s : ℝ} (hs : 0 < s) :
    μ (ball (0 : E) s) = ENNReal.ofReal (s ^ (finrank ℝ E : ℝ)) * μ (ball (0 : E) 1) := by
  have h := lintegral_ball_hom (μ := μ) (P := fun _ : E => (1 : ℝ)) (fun _ => zero_le_one)
    measurable_const (k := 0) (fun c hc x => by simp) hs
  simpa [Real.one_rpow] using h

/-! ## The pointwise layer identity -/

/-- **The layer identity.** For `x ≠ 0` and `r > 0`,
`min (‖x‖^{-d-α}) (r^{-d-α}) = (d+α) ∫_{max (r, ‖x‖)}^∞ s^{-d-α-1} ds`,
written as a `ℝ≥0∞`-valued integral over the parameter `s`. -/
theorem min_rpow_eq_lintegral {α r : ℝ} (hα : 0 < α) (hr : 0 < r) {x : E} (hx : x ≠ 0) :
    ENNReal.ofReal (min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (r ^ (-(finrank ℝ E : ℝ) - α)))
      = ∫⁻ s, (if r < s ∧ ‖x‖ < s then
          ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0) := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hx0 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hz : -(finrank ℝ E : ℝ) - α ≤ 0 := by linarith
  rcases le_or_gt ‖x‖ r with hxr | hxr
  · -- `‖x‖ ≤ r`: the minimum is `r^{-d-α}` and the layer integral starts at `r`
    have hmin : min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (r ^ (-(finrank ℝ E : ℝ) - α))
        = r ^ (-(finrank ℝ E : ℝ) - α) :=
      min_eq_right (Real.rpow_le_rpow_of_nonpos hx0 hxr hz)
    rw [hmin]
    have hsupp : (fun s : ℝ => if r < s ∧ ‖x‖ < s then
        ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0)
        = (Ioi r).indicator (fun t : ℝ =>
          ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * t ^ (-(finrank ℝ E : ℝ) - α - 1))) := by
      funext s
      rw [Set.indicator_apply]
      by_cases hs : r < s
      · rw [ite_eq_left ⟨hs, lt_of_le_of_lt hxr hs⟩, ite_eq_left (show s ∈ Ioi r from hs)]
      · rw [ite_eq_right (fun h : r < s ∧ ‖x‖ < s => hs h.1),
          ite_eq_right (show s ∉ Ioi r from fun h => hs h)]
    rw [hsupp, lintegral_indicator measurableSet_Ioi, lintegral_Ioi_levy_layer hα hr]
  · -- `r < ‖x‖`: the minimum is `‖x‖^{-d-α}` and the layer integral starts at `‖x‖`
    have hmin : min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (r ^ (-(finrank ℝ E : ℝ) - α))
        = ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) :=
      min_eq_left (Real.rpow_le_rpow_of_nonpos hr hxr.le hz)
    rw [hmin]
    have hsupp : (fun s : ℝ => if r < s ∧ ‖x‖ < s then
        ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0)
        = (Ioi ‖x‖).indicator (fun t : ℝ =>
          ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * t ^ (-(finrank ℝ E : ℝ) - α - 1))) := by
      funext s
      rw [Set.indicator_apply]
      by_cases hs : ‖x‖ < s
      · rw [ite_eq_left ⟨lt_trans hxr hs, hs⟩, ite_eq_left (show s ∈ Ioi ‖x‖ from hs)]
      · rw [ite_eq_right (fun h : r < s ∧ ‖x‖ < s => hs h.2),
          ite_eq_right (show s ∉ Ioi ‖x‖ from fun h => hs h)]
    rw [hsupp, lintegral_indicator measurableSet_Ioi, lintegral_Ioi_levy_layer hα hx0]

/-! ## The mass of `min (‖x‖^{-d-α}) (r^{-d-α})` -/

/-- Measurability of the layer integrand. -/
theorem measurable_levy_layer (α r : ℝ) :
    Measurable (Function.uncurry (fun (x : E) (s : ℝ) =>
      if r < s ∧ ‖x‖ < s then
        ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0)) := by
  have : Function.uncurry (fun (x : E) (s : ℝ) =>
      if r < s ∧ ‖x‖ < s then
        ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0)
      = fun p : E × ℝ => if r < p.2 ∧ ‖p.1‖ < p.2 then
        ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * p.2 ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0 := rfl
  rw [this]
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt (measurable_norm.comp measurable_fst) measurable_snd)
  · fun_prop

/-- **The mass identity for the minimum**: for `α, r > 0`,
`∫ min (‖x‖^{-d-α}) (r^{-d-α}) dx = ((d+α)/α) r^{-α} |B_1|`. -/
theorem lintegral_min_rpow (μ : Measure E) [μ.IsAddHaarMeasure] {α r : ℝ} (hα : 0 < α)
    (hr : 0 < r) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (r ^ (-(finrank ℝ E : ℝ) - α)))
      ∂μ = ENNReal.ofReal (((finrank ℝ E : ℝ) + α) / α * r ^ (-α)) * μ (ball (0 : E) 1) := by
  classical
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hc : (0 : ℝ) < (finrank ℝ E : ℝ) + α := by linarith
  -- rewrite pointwise (a.e.) as a layer integral
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal
      (min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (r ^ (-(finrank ℝ E : ℝ) - α)))
      = ∫⁻ s, (if r < s ∧ ‖x‖ < s then
          ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0) :=
    (ae_ne_zero (E := E) μ).mono fun x hx => min_rpow_eq_lintegral hα hr hx
  rw [lintegral_congr_ae hpt]
  -- Tonelli
  rw [lintegral_lintegral_swap (measurable_levy_layer (E := E) α r).aemeasurable]
  -- the inner `x`-integral for fixed `s`
  have hinner : ∀ s : ℝ, ∫⁻ x, (if r < s ∧ ‖x‖ < s then
      ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0) ∂μ
      = (Ioi r).indicator (fun t : ℝ =>
          ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * t ^ (-α - 1)) * μ (ball (0 : E) 1)) s := by
    intro s
    by_cases hs : r < s
    · have hspos : (0 : ℝ) < s := lt_trans hr hs
      have hK : (0 : ℝ) ≤ (finrank ℝ E : ℝ) + α := hc.le
      have hsnn : (0 : ℝ) ≤ s ^ (-(finrank ℝ E : ℝ) - α - 1) := Real.rpow_nonneg hspos.le _
      have hsd : (0 : ℝ) ≤ s ^ (finrank ℝ E : ℝ) := Real.rpow_nonneg hspos.le _
      have harith : ((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)
          * s ^ (finrank ℝ E : ℝ) = ((finrank ℝ E : ℝ) + α) * s ^ (-α - 1) := by
        rw [mul_assoc, ← Real.rpow_add hspos]
        congr 2
        ring
      have hsupp : (fun x : E => if r < s ∧ ‖x‖ < s then
          ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0)
          = (ball (0 : E) s).indicator (fun _ : E =>
            ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1))) := by
        funext x
        rw [Set.indicator_apply]
        by_cases hx : x ∈ ball (0 : E) s
        · have hxs : ‖x‖ < s := by simpa [mem_ball, dist_zero_right] using hx
          rw [ite_eq_left ⟨hs, hxs⟩, ite_eq_left hx]
        · have hxs : ¬ ‖x‖ < s := fun h => hx (by simpa [mem_ball, dist_zero_right] using h)
          rw [ite_eq_right (fun h : r < s ∧ ‖x‖ < s => hxs h.2), ite_eq_right hx]
      rw [hsupp, lintegral_indicator measurableSet_ball, setLIntegral_const,
        measure_ball_eq_ofReal_mul μ hspos,
        Set.indicator_of_mem (show s ∈ Ioi r from hs)]
      have hstep : ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1))
          * ENNReal.ofReal (s ^ (finrank ℝ E : ℝ))
          = ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-α - 1)) := by
        rw [← harith]
        have hK2 : (0 : ℝ) ≤ ((finrank ℝ E : ℝ) + α)
            * s ^ (-(finrank ℝ E : ℝ) - α - 1) := mul_nonneg hK hsnn
        exact (ENNReal.ofReal_mul (q := s ^ (finrank ℝ E : ℝ)) hK2).symm
      rw [← mul_assoc, hstep]
    · have hzero : ∀ x : E, (if r < s ∧ ‖x‖ < s then
          ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-(finrank ℝ E : ℝ) - α - 1)) else 0) = 0 := by
        intro x
        rw [ite_eq_right (fun h : r < s ∧ ‖x‖ < s => hs h.1)]
      rw [lintegral_congr hzero, lintegral_zero,
        Set.indicator_of_notMem (show s ∉ Ioi r from fun h => hs h)]
  rw [lintegral_congr hinner, lintegral_indicator measurableSet_Ioi]
  have hmeas : Measurable (fun s : ℝ =>
      ENNReal.ofReal (((finrank ℝ E : ℝ) + α) * s ^ (-α - 1))) := by fun_prop
  rw [lintegral_mul_const _ hmeas, lintegral_Ioi_levy_tail hα hr]
  congr 1
  congr 1
  ring

/-! ## The mass of the density gap: (I.5.18) -/

/-- **The mass of the density gap**: `∫ (dΠ_∞/dx - dΠ_lam/dx) dx = lam^{-α} |B_1|`.

This is the sharp form of (I.5.18) (the case `lam = 1`): the number of additional jumps when
passing from the truncated Lévy process to the `α`-stable one is one, under the paper's
normalisation `|B_1| = 1`. -/
theorem lintegral_levyDens_gap (μ : Measure E) [μ.IsAddHaarMeasure] {α r : ℝ} (hα : 0 < α)
    (hr : 0 < r) :
    ∫⁻ x, (levyDensInf (E := E) α x - levyDensLam (E := E) α r x) ∂μ
      = ENNReal.ofReal (r ^ (-α)) * μ (ball (0 : E) 1) := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hc : (0 : ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) := div_nonneg hα.le (by linarith)
  have hmeas : Measurable (fun x : E => ENNReal.ofReal
      (min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (r ^ (-(finrank ℝ E : ℝ) - α)))) := by
    fun_prop
  have hpt : ∀ x : E, (levyDensInf (E := E) α x - levyDensLam (E := E) α r x)
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * (ENNReal.ofReal (min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α))
            (r ^ (-(finrank ℝ E : ℝ) - α)))) := by
    intro x
    rw [levyDens_gap_eq hα hr, ENNReal.ofReal_mul hc]
  rw [lintegral_congr hpt, lintegral_const_mul _ hmeas, lintegral_min_rpow μ hα hr,
    ← mul_assoc, ← ENNReal.ofReal_mul hc]
  congr 1
  have hαne : α ≠ 0 := hα.ne'
  have hdα : (finrank ℝ E : ℝ) + α ≠ 0 := by positivity
  field_simp

/-- **(I.5.18)**: `Π_∞ - Π_1` has total mass `|B_1|` (equal to `1` under the paper's
normalisation `|B_1| = 1`). -/
theorem lintegral_levyDens_gap_one (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) :
    ∫⁻ x, (levyDensInf (E := E) α x - levyDensOne (E := E) α x) ∂μ = μ (ball (0 : E) 1) := by
  have h := lintegral_levyDens_gap (E := E) μ (r := 1) hα one_pos
  simpa [levyDensOne, Real.one_rpow] using h

end PercLib.CriticalLRP.LevyAnalysis
