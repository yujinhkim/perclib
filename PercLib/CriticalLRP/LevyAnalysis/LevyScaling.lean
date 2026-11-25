/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I: High effective
dimension", arXiv:2508.18807v1, Section I.5.2.

Dilation (self-similarity) identities for the Lévy measures of (I.5.16):

* `Π_∞` is homogeneous of degree `α`: `map (x ↦ c x) Π_∞ = c^α • Π_∞`;
* the truncated measures satisfy `Π_lam = lam^{-α} • map (x ↦ lam x) Π_1`.

The second identity is what makes the paper's display after (I.5.16),
`dΠ_lam/dx (x) = α 1(‖x‖ ≤ lam) ∫_{‖x‖}^{lam} s^{-d-α-1} ds`,
true: the density of `map (x ↦ lam x) Π_1` at `x` is `lam^{-d} ρ_1 (x/lam)`, so the multiplier is
`lam^{-d-α}` (the factor `lam^{d-α}` printed in the paper is inconsistent with the displayed
closed form `= α 1(‖x‖ ≤ lam) ∫_{‖x‖}^{lam}`; the two differ by `lam^{2d}`).
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.Measures
public import PercLib.CriticalLRP.LevyAnalysis.LevyGap
public import PercLib.CriticalLRP.LevyAnalysis.LevyMass

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

/-! ## The substitution formula for dilations -/

/-- Dilation substitution for `ℝ≥0∞`-integrals:
`∫ g (c x) φ x dx = c^{-d} ∫ g y φ (y/c) dy`. -/
theorem lintegral_comp_const_smul_mul (μ : Measure E) [μ.IsAddHaarMeasure] {c : ℝ} (hc : 0 < c)
    {g φ : E → ℝ≥0∞} (hg : Measurable g) (hφ : Measurable φ) :
    ∫⁻ x, g (c • x) * φ x ∂μ
      = ENNReal.ofReal (c ^ (-(finrank ℝ E : ℝ))) * ∫⁻ y, g y * φ (c⁻¹ • y) ∂μ := by
  have hmeas : Measurable fun x : E => φ (c⁻¹ • x) := hφ.comp (measurable_const_smul c⁻¹)
  have h := lintegral_inv_smul (μ := μ) c⁻¹ (inv_pos.2 hc)
    (fun y : E => g y * φ (c⁻¹ • y)) (hg.mul hmeas)
  rw [inv_inv] at h
  have hleft : ∀ x : E, (fun y : E => g y * φ (c⁻¹ • y)) (c • x) = g (c • x) * φ x := by
    intro x
    simp only
    rw [inv_smul_smul₀ hc.ne']
  rw [show (∫⁻ x, g (c • x) * φ x ∂μ)
      = ∫⁻ x, (fun y : E => g y * φ (c⁻¹ • y)) (c • x) ∂μ from
    lintegral_congr fun x => (hleft x).symm]
  rw [h]
  congr 1
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hc.le]

/-- The density of the pushforward of `f dμ` under `x ↦ c x`: `c^{-d} f (x/c)`. -/
theorem map_const_smul_withDensity (μ : Measure E) [μ.IsAddHaarMeasure] {c : ℝ} (hc : 0 < c)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    Measure.map (fun x => c • x) (μ.withDensity f)
      = μ.withDensity (fun y => ENNReal.ofReal (c ^ (-(finrank ℝ E : ℝ))) * f (c⁻¹ • y)) := by
  classical
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_smul c) hs,
    withDensity_apply _ (measurable_const_smul c hs), withDensity_apply _ hs]
  have hg : Measurable (s.indicator (fun _ : E => (1 : ℝ≥0∞))) := measurable_const.indicator hs
  have hpf : Measurable fun y : E => f (c⁻¹ • y) := hf.comp (measurable_const_smul c⁻¹)
  calc ∫⁻ x in (fun x : E => c • x) ⁻¹' s, f x ∂μ
      = ∫⁻ x, (s.indicator (fun _ : E => (1 : ℝ≥0∞))) (c • x) * f x ∂μ := by
        rw [← lintegral_indicator (measurable_const_smul c hs)]
        refine lintegral_congr fun x => ?_
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases hx : x ∈ (fun x : E => c • x) ⁻¹' s
        · have hx' : c • x ∈ s := hx
          rw [ite_eq_left hx, ite_eq_left hx', one_mul]
        · have hx' : c • x ∉ s := hx
          rw [ite_eq_right hx, ite_eq_right hx', zero_mul]
    _ = ENNReal.ofReal (c ^ (-(finrank ℝ E : ℝ)))
          * ∫⁻ y, (s.indicator (fun _ : E => (1 : ℝ≥0∞))) y * f (c⁻¹ • y) ∂μ :=
        lintegral_comp_const_smul_mul μ hc hg hf
    _ = ENNReal.ofReal (c ^ (-(finrank ℝ E : ℝ))) * ∫⁻ y in s, f (c⁻¹ • y) ∂μ := by
        congr 1
        rw [← lintegral_indicator hs]
        refine lintegral_congr fun y => ?_
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases hy : y ∈ s
        · rw [ite_eq_left hy, ite_eq_left hy, one_mul]
        · rw [ite_eq_right hy, ite_eq_right hy, zero_mul]
    _ = ∫⁻ y in s, ENNReal.ofReal (c ^ (-(finrank ℝ E : ℝ))) * f (c⁻¹ • y) ∂μ := by
        rw [lintegral_const_mul _ hpf]

/-! ## Self-similarity of `Π_∞` -/

/-- The `Π_∞`-density scales as `ρ_∞ (x/c) = c^{d+α} ρ_∞ (x)`. -/
theorem levyRealInf_comp_inv_smul {α : ℝ} (hα : 0 < α) {c : ℝ} (hc : 0 < c) (y : E) :
    levyRealInf (E := E) α (c⁻¹ • y)
      = c ^ ((finrank ℝ E : ℝ) + α) * levyRealInf (E := E) α y := by
  have hnorm : ‖c⁻¹ • y‖ = c⁻¹ * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
  have hrpow : ‖c⁻¹ • y‖ ^ (-(finrank ℝ E : ℝ) - α)
      = c ^ ((finrank ℝ E : ℝ) + α) * ‖y‖ ^ (-(finrank ℝ E : ℝ) - α) := by
    rw [hnorm, Real.mul_rpow (inv_pos.2 hc).le (norm_nonneg y), Real.inv_rpow hc.le,
      ← Real.rpow_neg hc.le]
    congr 1
    ring
  unfold levyRealInf
  rw [hrpow]
  ring

/-- The `Π_∞`-density scales as `ρ_∞ (x/c) = c^{d+α} ρ_∞ (x)`, in `ℝ≥0∞`. -/
theorem levyDensInf_comp_inv_smul {α : ℝ} (hα : 0 < α) {c : ℝ} (hc : 0 < c) (y : E) :
    levyDensInf (E := E) α (c⁻¹ • y)
      = ENNReal.ofReal (c ^ ((finrank ℝ E : ℝ) + α)) * levyDensInf (E := E) α y := by
  have hca : (0 : ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) := div_nonneg hα.le (by linarith)
  have hreal : α / ((finrank ℝ E : ℝ) + α) * ‖c⁻¹ • y‖ ^ (-(finrank ℝ E : ℝ) - α)
      = c ^ ((finrank ℝ E : ℝ) + α)
        * (α / ((finrank ℝ E : ℝ) + α) * ‖y‖ ^ (-(finrank ℝ E : ℝ) - α)) := by
    simpa only [levyRealInf] using levyRealInf_comp_inv_smul (E := E) hα hc y
  rw [levyDensInf, levyDensInf, hreal, ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]

/-- **Self-similarity of the `α`-stable Lévy measure**: `map (x ↦ c x) Π_∞ = c^α • Π_∞`. -/
theorem map_const_smul_PiInf (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    {c : ℝ} (hc : 0 < c) :
    Measure.map (fun x => c • x) (PiInf (E := E) α μ)
      = ENNReal.ofReal (c ^ α) • PiInf (E := E) α μ := by
  have hf : Measurable (levyDensInf (E := E) α) := measurable_levyDensInf α
  simp only [PiInf]
  rw [map_const_smul_withDensity μ hc hf]
  have hdens : (fun y : E => ENNReal.ofReal (c ^ (-(finrank ℝ E : ℝ)))
        * levyDensInf (E := E) α (c⁻¹ • y))
      = fun y : E => ENNReal.ofReal (c ^ α) * levyDensInf (E := E) α y := by
    funext y
    rw [levyDensInf_comp_inv_smul hα hc y, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
      show c ^ (-(finrank ℝ E : ℝ)) * c ^ ((finrank ℝ E : ℝ) + α) = c ^ α by
        rw [← Real.rpow_add hc]
        congr 1
        ring]
  rw [hdens, ← withDensity_smul (ENNReal.ofReal (c ^ α)) hf]
  rfl

/-! ## The truncated measures are dilated copies of `Π_1` -/

/-- The `Π_1`-density in un-truncated (raw) form. -/
theorem levyDensOne_eq_ofReal_raw {α : ℝ} (x : E) :
    levyDensOne (E := E) α x
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)
        * (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - 1)) := by
  simp only [levyDensOne, levyDensLam, Real.one_rpow]

/-- The `Π_lam`-density in un-truncated (raw) form. -/
theorem levyDensLam_eq_ofReal_raw (α lam : ℝ) (x : E) :
    levyDensLam (E := E) α lam x
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)
        * (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α))) := rfl

/-- **The dilation identity for the truncated densities** (raw form):
`c^{-d} ρ_1 (x/c) = c^α ρ_c (x)`, i.e. the density of `x ↦ c x` applied to `Π_1` is `c^α` times
the density of `Π_c`. -/
theorem levyDensOne_comp_inv_smul {α : ℝ} (hα : 0 < α) {c : ℝ} (hc : 0 < c) (y : E) :
    ENNReal.ofReal (c ^ (-(finrank ℝ E : ℝ))) * levyDensOne (E := E) α (c⁻¹ • y)
      = ENNReal.ofReal (c ^ α) * levyDensLam (E := E) α c y := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hnorm : ‖c⁻¹ • y‖ = c⁻¹ * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
  have hrpow : ‖c⁻¹ • y‖ ^ (-(finrank ℝ E : ℝ) - α)
      = c ^ ((finrank ℝ E : ℝ) + α) * ‖y‖ ^ (-(finrank ℝ E : ℝ) - α) := by
    rw [hnorm, Real.mul_rpow (inv_pos.2 hc).le (norm_nonneg y), Real.inv_rpow hc.le,
      ← Real.rpow_neg hc.le]
    congr 1
    ring
  have hAB : c ^ (-(finrank ℝ E : ℝ)) * c ^ ((finrank ℝ E : ℝ) + α) = c ^ α := by
    rw [← Real.rpow_add hc]
    congr 1
    ring
  have hAS : c ^ α * c ^ (-(finrank ℝ E : ℝ) - α) = c ^ (-(finrank ℝ E : ℝ)) := by
    rw [← Real.rpow_add hc]
    congr 1
    ring
  have hreal : c ^ (-(finrank ℝ E : ℝ))
        * (α / ((finrank ℝ E : ℝ) + α) * (‖c⁻¹ • y‖ ^ (-(finrank ℝ E : ℝ) - α) - 1))
      = c ^ α * (α / ((finrank ℝ E : ℝ) + α)
        * (‖y‖ ^ (-(finrank ℝ E : ℝ) - α) - c ^ (-(finrank ℝ E : ℝ) - α))) := by
    rw [hrpow]
    calc c ^ (-(finrank ℝ E : ℝ)) * (α / ((finrank ℝ E : ℝ) + α)
          * (c ^ ((finrank ℝ E : ℝ) + α) * ‖y‖ ^ (-(finrank ℝ E : ℝ) - α) - 1))
        = α / ((finrank ℝ E : ℝ) + α)
          * ((c ^ (-(finrank ℝ E : ℝ)) * c ^ ((finrank ℝ E : ℝ) + α))
              * ‖y‖ ^ (-(finrank ℝ E : ℝ) - α) - c ^ (-(finrank ℝ E : ℝ))) := by ring
      _ = α / ((finrank ℝ E : ℝ) + α)
          * (c ^ α * ‖y‖ ^ (-(finrank ℝ E : ℝ) - α) - c ^ (-(finrank ℝ E : ℝ))) := by rw [hAB]
      _ = c ^ α * (α / ((finrank ℝ E : ℝ) + α)
          * (‖y‖ ^ (-(finrank ℝ E : ℝ) - α) - c ^ (-(finrank ℝ E : ℝ) - α))) := by
          rw [← hAS]; ring
  rw [levyDensOne_eq_ofReal_raw, levyDensLam_eq_ofReal_raw,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), hreal,
    ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]

/-- **The dilated cut-off measures**: `Π_lam = lam^{-α} • map (x ↦ lam x) Π_1`. -/
theorem PiLam_eq_smul_map_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α lam : ℝ} (hα : 0 < α)
    (hlam : 0 < lam) :
    PiLam (E := E) α lam μ
      = ENNReal.ofReal (lam ^ (-α)) • Measure.map (fun x => lam • x) (PiOne (E := E) α μ) := by
  have hone : Measurable (levyDensLam (E := E) α 1) := measurable_levyDensLam α 1
  have hlam' : Measurable (levyDensLam (E := E) α lam) := measurable_levyDensLam α lam
  have hden : (fun y : E => ENNReal.ofReal (lam ^ (-(finrank ℝ E : ℝ)))
        * levyDensLam (E := E) α 1 (lam⁻¹ • y))
      = (ENNReal.ofReal (lam ^ α) • levyDensLam (E := E) α lam) := by
    funext y
    exact levyDensOne_comp_inv_smul (E := E) hα hlam y
  have hpow : lam ^ (-α) * lam ^ α = (1 : ℝ) := by
    rw [← Real.rpow_add hlam]
    simp
  simp only [PiOne, PiLam]
  rw [map_const_smul_withDensity μ hlam hone, hden, withDensity_smul _ hlam', smul_smul,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _), hpow, ENNReal.ofReal_one, one_smul]

end PercLib.CriticalLRP.LevyAnalysis
