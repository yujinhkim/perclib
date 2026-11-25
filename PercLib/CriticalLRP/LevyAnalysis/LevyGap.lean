/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I: High effective
dimension", arXiv:2508.18807v1, Section I.5.2.

This file records the *real-valued* shape of the Lévy densities of (I.5.16), the exact pointwise
form of the density gap between `Π_lam` and `Π_∞`, the resulting uniform (`L∞`) convergence
`dΠ_lam/dx → dΠ_∞/dx`, the pointwise `lam`-derivative identities (I.5.19), and the differentiated
mass identity (I.5.20).
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.Measures

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

/-! ## Real-valued versions of the densities (I.5.16) -/

/-- The real-valued density of `Π_∞`: `α/(d+α) ‖x‖^{-d-α}`. -/
noncomputable def levyRealInf (α : ℝ) (x : E) : ℝ :=
  α / ((finrank ℝ E : ℝ) + α) * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α)

/-- The real-valued density of `Π_lam` *truncated at zero*, i.e. the largest nonnegative function
whose `ENNReal.ofReal` is the density `α/(d+α)(‖x‖^{-d-α} - lam^{-d-α}) 1(‖x‖ ≤ lam)`. -/
noncomputable def levyRealLam (α lam : ℝ) (x : E) : ℝ :=
  α / ((finrank ℝ E : ℝ) + α) *
    max (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α)) 0

theorem levyDensInf_eq_ofReal (α : ℝ) (x : E) :
    levyDensInf (E := E) α x = ENNReal.ofReal (levyRealInf (E := E) α x) := rfl

/-- The `Π_lam`-density is `ofReal` of its truncated real-valued version. -/
theorem levyDensLam_eq_ofReal {α lam : ℝ} (hα : 0 < α) (x : E) :
    levyDensLam (E := E) α lam x = ENNReal.ofReal (levyRealLam (E := E) α lam x) := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hc : (0 : ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) :=
    div_nonneg hα.le (by linarith)
  have hmax : α / ((finrank ℝ E : ℝ) + α) *
      max (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α)) 0
      = max (α / ((finrank ℝ E : ℝ) + α) *
        (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α))) 0 := by
    rw [mul_max_of_nonneg _ _ hc, mul_zero]
  show ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)
      * (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α)))
    = ENNReal.ofReal (levyRealLam (E := E) α lam x)
  rw [levyRealLam, hmax]
  by_cases h : 0 ≤ α / ((finrank ℝ E : ℝ) + α) *
      (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α))
  · rw [max_eq_left h]
  · rw [max_eq_right (le_of_lt (not_le.mp h)), ENNReal.ofReal_eq_zero.mpr (le_of_lt (not_le.mp h))]
    simp

theorem measurable_levyRealInf (α : ℝ) : Measurable (levyRealInf (E := E) α) := by
  unfold levyRealInf; fun_prop

theorem measurable_levyRealLam (α lam : ℝ) : Measurable (levyRealLam (E := E) α lam) := by
  unfold levyRealLam; fun_prop

theorem levyRealInf_nonneg {α : ℝ} (hα : 0 < α) (x : E) : 0 ≤ levyRealInf (E := E) α x := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hc : (0 : ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) :=
    div_nonneg hα.le (by linarith)
  exact mul_nonneg hc (Real.rpow_nonneg (norm_nonneg x) _)

/-- Real arithmetic behind the density gap: for `a, f, g ≥ 0`,
`a f - max (a (f - g)) 0 = a * min f g`. -/
theorem mul_sub_max_zero {a f g : ℝ} (ha : 0 ≤ a) (hg : 0 ≤ g) :
    a * f - max (a * (f - g)) 0 = a * min f g := by
  rcases le_total g f with h | h
  · have h1 : 0 ≤ a * (f - g) := mul_nonneg ha (by linarith)
    rw [max_eq_left h1, min_eq_right h]
    ring
  · have h1 : a * (f - g) ≤ 0 := by nlinarith
    rw [max_eq_right h1, min_eq_left h]
    ring

/-- **The density gap, exactly.** For `lam > 0` and `α > 0`,
`dΠ_∞/dx - dΠ_lam/dx = α/(d+α) * min (‖x‖^{-d-α}) (lam^{-d-α})`, the paper's integrand in
(I.5.18) (the case `lam = 1`). -/
theorem levyReal_gap {α lam : ℝ} (hα : 0 < α) (hlam : 0 < lam) (x : E) :
    levyRealInf (E := E) α x - levyRealLam (E := E) α lam x
      = α / ((finrank ℝ E : ℝ) + α) *
        min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (lam ^ (-(finrank ℝ E : ℝ) - α)) := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hc : (0 : ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) :=
    div_nonneg hα.le (by linarith)
  have hmax : α / ((finrank ℝ E : ℝ) + α) *
      max (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α)) 0
      = max (α / ((finrank ℝ E : ℝ) + α) *
        (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α))) 0 := by
    rw [mul_max_of_nonneg _ _ hc, mul_zero]
  unfold levyRealInf levyRealLam
  rw [hmax]
  exact mul_sub_max_zero hc (Real.rpow_nonneg hlam.le _)

/-- The `ℝ≥0∞`-valued density gap equals `ofReal` of the real gap. -/
theorem levyDens_gap_eq {α lam : ℝ} (hα : 0 < α) (hlam : 0 < lam) (x : E) :
    levyDensInf (E := E) α x - levyDensLam (E := E) α lam x
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)
          * min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (lam ^ (-(finrank ℝ E : ℝ) - α))) := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hc : (0 : ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) :=
    div_nonneg hα.le (by linarith)
  have h3 : 0 ≤ α / ((finrank ℝ E : ℝ) + α)
      * min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (lam ^ (-(finrank ℝ E : ℝ) - α)) :=
    mul_nonneg hc (le_min (Real.rpow_nonneg (norm_nonneg x) _)
      (Real.rpow_nonneg hlam.le _))
  have hle : levyRealLam (E := E) α lam x ≤ levyRealInf (E := E) α x := by
    have h := levyReal_gap hα hlam x
    linarith
  have hL : (0 : ℝ) ≤ levyRealLam (E := E) α lam x := by
    rw [levyRealLam]
    exact mul_nonneg hc (le_max_right _ _)
  rw [levyDensInf_eq_ofReal, levyDensLam_eq_ofReal hα,
    ← ENNReal.ofReal_sub (levyRealInf (E := E) α x) hL, levyReal_gap hα hlam]

/-- Pointwise domination `dΠ_lam/dx ≤ dΠ_∞/dx`. -/
theorem levyDensLam_le_levyDensInf {α lam : ℝ} (hα : 0 < α) (hlam : 0 < lam) (x : E) :
    levyDensLam (E := E) α lam x ≤ levyDensInf (E := E) α x := by
  have hc : (0 : ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) := div_nonneg hα.le (by linarith)
  rw [levyDensInf_eq_ofReal, levyDensLam_eq_ofReal hα]
  apply ENNReal.ofReal_le_ofReal
  unfold levyRealLam levyRealInf
  refine mul_le_mul_of_nonneg_left (max_le ?_ (Real.rpow_nonneg (norm_nonneg x) _)) hc
  linarith [Real.rpow_nonneg hlam.le (-(finrank ℝ E : ℝ) - α)]

/-- **Uniform convergence of the densities** (the `L∞` convergence of Section I.5.2):
for every `ε > 0` and all `lam` large enough, the pointwise gap between the `Π_lam`-density and
the `Π_∞`-density is at most `ε`, uniformly in `x`. -/
theorem levyDens_gap_tendsto_uniform {α : ℝ} (hα : 0 < α) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ lam : ℝ in atTop, ∀ x : E,
      levyDensInf (E := E) α x - levyDensLam (E := E) α lam x ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hc : (0 : ℝ) < α / ((finrank ℝ E : ℝ) + α) :=
    div_pos hα (by linarith)
  have h' : Tendsto (fun lam : ℝ => lam ^ (-(finrank ℝ E : ℝ) - α)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := (finrank ℝ E : ℝ) + α) (by linarith)
    have he : (-((finrank ℝ E : ℝ) + α)) = -(finrank ℝ E : ℝ) - α := by ring
    rwa [he] at h
  have h0 : Tendsto (fun lam : ℝ => α / ((finrank ℝ E : ℝ) + α)
      * lam ^ (-(finrank ℝ E : ℝ) - α)) atTop (𝓝 0) := by
    simpa using h'.const_mul (α / ((finrank ℝ E : ℝ) + α))
  have h1 : ∀ᶠ lam : ℝ in atTop,
      α / ((finrank ℝ E : ℝ) + α) * lam ^ (-(finrank ℝ E : ℝ) - α) < ε :=
    h0.eventually_lt_const hε
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with lam hlam hlam1
  intro x
  have hpos : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam1
  calc levyDensInf (E := E) α x - levyDensLam (E := E) α lam x
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)
          * min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (lam ^ (-(finrank ℝ E : ℝ) - α))) :=
        levyDens_gap_eq hα hpos x
    _ ≤ ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α) * lam ^ (-(finrank ℝ E : ℝ) - α)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hlam.le

/-! ## The `lam`-derivative of the density (I.5.19) -/

/-- **(I.5.19)** inside the support: for `0 < ‖x‖ < lam` the `lam`-derivative of the
`Π_lam`-density is `α lam^{-d-α-1}`. -/
theorem hasDerivAt_levyRealLam_of_lt {α : ℝ} (hα : 0 < α) {x : E} (hx : x ≠ 0) {lam : ℝ}
    (hxlam : ‖x‖ < lam) :
    HasDerivAt (fun l : ℝ => levyRealLam (E := E) α l x)
      (α * lam ^ (-(finrank ℝ E : ℝ) - α - 1)) lam := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hq : (-(finrank ℝ E : ℝ) - α) ≠ 0 := by linarith
  have hx0 : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hderiv : HasDerivAt (fun l : ℝ => l ^ (-(finrank ℝ E : ℝ) - α))
      ((-(finrank ℝ E : ℝ) - α) * lam ^ (-(finrank ℝ E : ℝ) - α - 1)) lam :=
    Real.hasDerivAt_rpow_const (Or.inl (lt_of_le_of_lt (norm_nonneg x) hxlam).ne')
  have hconst : HasDerivAt (fun _ : ℝ => ‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) 0 lam :=
    hasDerivAt_const lam _
  have hfun : HasDerivAt (fun l : ℝ => ‖x‖ ^ (-(finrank ℝ E : ℝ) - α)
      - l ^ (-(finrank ℝ E : ℝ) - α))
      (0 - (-(finrank ℝ E : ℝ) - α) * lam ^ (-(finrank ℝ E : ℝ) - α - 1)) lam :=
    hconst.sub hderiv
  have hpos : 0 < ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α) := by
    have h1 : lam ^ (-(finrank ℝ E : ℝ) - α) < ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) :=
      Real.rpow_lt_rpow_of_neg hx0 hxlam (by linarith)
    linarith
  have hev : (fun l : ℝ => ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - l ^ (-(finrank ℝ E : ℝ) - α))
      =ᶠ[𝓝 lam] (fun l : ℝ => max (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)
        - l ^ (-(finrank ℝ E : ℝ) - α)) 0) := by
    filter_upwards [hfun.continuousAt.eventually (eventually_gt_nhds hpos)] with l hl
    exact (max_eq_left hl.le).symm
  have hmax := hfun.congr_of_eventuallyEq hev.symm
  have hfinal := hmax.const_mul (α / ((finrank ℝ E : ℝ) + α))
  have hmul : (fun l : ℝ => α / ((finrank ℝ E : ℝ) + α) * max (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)
      - l ^ (-(finrank ℝ E : ℝ) - α)) 0) = (fun l : ℝ => levyRealLam (E := E) α l x) := rfl
  rw [hmul] at hfinal
  convert hfinal using 1
  have hpos' : (0 : ℝ) < lam ^ (-(finrank ℝ E : ℝ) - α - 1) :=
    Real.rpow_pos_of_pos (lt_of_le_of_lt (norm_nonneg x) hxlam) _
  field_simp
  ring

/-- **(I.5.19)** outside the support: for `0 < lam < ‖x‖` the `Π_lam`-density is identically zero
in a neighbourhood of `lam`, hence its `lam`-derivative vanishes. -/
theorem hasDerivAt_levyRealLam_of_gt {α : ℝ} (hα : 0 < α) {x : E} {lam : ℝ} (hlam : 0 < lam)
    (hlamx : lam < ‖x‖) :
    HasDerivAt (fun l : ℝ => levyRealLam (E := E) α l x) 0 lam := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hev : ∀ l ∈ Set.Ioo (0 : ℝ) ‖x‖, levyRealLam (E := E) α l x = 0 := by
    intro l hl
    have h1 : ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) ≤ l ^ (-(finrank ℝ E : ℝ) - α) :=
      Real.rpow_le_rpow_of_nonpos hl.1 hl.2.le (by linarith)
    have h2 : ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - l ^ (-(finrank ℝ E : ℝ) - α) ≤ 0 := by linarith
    rw [levyRealLam, max_eq_right h2, mul_zero]
  have hnhds : Set.Ioo (0 : ℝ) ‖x‖ ∈ 𝓝 lam := Ioo_mem_nhds hlam hlamx
  have hev' : (fun l : ℝ => levyRealLam (E := E) α l x) =ᶠ[𝓝 lam] (fun _ => 0) :=
    Filter.eventually_of_mem hnhds hev
  exact (hasDerivAt_const (x := lam) (c := 0)).congr_of_eventuallyEq hev'

/-! ## The differentiated mass identity (I.5.20) -/

/-- **(I.5.20)**: the total mass of the `lam`-derivative of the density is `α lam^{-α-1} |B_1|`.
Note that `Π_lam(ℝ^d) = +∞` for every `lam` (its density is not integrable at the origin), so the
identity can only hold for the derivative mass, which is what we prove. -/
theorem lintegral_levyDens_deriv (μ : Measure E) [μ.IsAddHaarMeasure] {α lam : ℝ} (hα : 0 < α)
    (hlam : 0 < lam) :
    ∫⁻ x in ball (0 : E) lam, ENNReal.ofReal (α * lam ^ (-(finrank ℝ E : ℝ) - α - 1)) ∂μ
      = ENNReal.ofReal (α * lam ^ (-α - 1)) * μ (ball (0 : E) 1) := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hconst : ∫⁻ x in ball (0 : E) lam, ENNReal.ofReal (α * lam ^ (-(finrank ℝ E : ℝ) - α - 1))
      ∂μ = ENNReal.ofReal (α * lam ^ (-(finrank ℝ E : ℝ) - α - 1)) * μ (ball (0 : E) lam) :=
    setLIntegral_const _ _
  have hball : μ (ball (0 : E) lam) = ENNReal.ofReal (lam ^ (finrank ℝ E : ℝ)) * μ (ball (0 : E) 1) := by
    have h := lintegral_ball_hom (μ := μ) (P := fun _ : E => (1 : ℝ)) (fun _ => zero_le_one)
      measurable_const (k := 0) (fun c hc x => by simp) hlam
    simpa [Real.one_rpow] using h
  have hαlam : (0 : ℝ) ≤ α * lam ^ (-(finrank ℝ E : ℝ) - α - 1) :=
    mul_nonneg hα.le (Real.rpow_nonneg hlam.le _)
  have hexp : -(finrank ℝ E : ℝ) - α - 1 + (finrank ℝ E : ℝ) = -α - 1 := by ring
  have harith : α * lam ^ (-(finrank ℝ E : ℝ) - α - 1) * lam ^ (finrank ℝ E : ℝ)
      = α * lam ^ (-α - 1) := by
    rw [mul_assoc, ← Real.rpow_add hlam, hexp]
  rw [hconst, hball, ← mul_assoc, ← ENNReal.ofReal_mul hαlam, harith]

end PercLib.CriticalLRP.LevyAnalysis
