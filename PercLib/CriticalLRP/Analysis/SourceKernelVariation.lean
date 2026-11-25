/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Exact asymptotics and regular variation of the source kernel

The source model states the kernel through its derivative,
`|K' s| = (1 + δ s) s^{-d-α-1}` with `δ → 0` and `δ` logarithmically integrable.
This module proves that the log-error factor averages out, so that

`K r · r^{d+α} → 1/(d+α)`  as `r → ∞`,

and consequently that `K` is regularly varying at `∞` of index `-(d+α)`, in the
repository's `RegularlyVaryingAtTop` sense.  The proof rewrites `K r` as the tail
integral of `|K'|`, rescales it to `[1,∞)` by `s = r t`, and passes to the limit
by dominated convergence with dominating function `2 t^{-d-α-1}`.

No statement about the cutoff mass, its continuity or its derivative is made.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.MomentMonotonicity.StrictCutoffEpsilon
public import PercLib.CriticalLRP.Analysis.RegularVariation
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Source-kernel parameters and regular variation -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

namespace SourceModelData

variable (M : SourceModelData)

/-- **Rescaled tail integral.**  With `δ` the logarithmic error factor of the
derivative, for `r > 0` the normalized profile is
`K r · r^{d+α} = ∫_{t>1} (1 + δ (r t)) t^{-d-α-1} dt`. -/
theorem K_mul_rpow_eq_integral (δ : ℝ → ℝ)
    (hδ : ∀ s : ℝ, 0 < s → |deriv M.K s| = (1 + δ s) * s ^ (-(M.d : ℝ) - M.α - 1))
    {r : ℝ} (hr : 0 < r) :
    M.K r * r ^ ((M.d : ℝ) + M.α)
      = ∫ t in Set.Ioi (1 : ℝ), (1 + δ (r * t)) * t ^ (-(M.d : ℝ) - M.α - 1) := by
  have hKr : M.K r = ∫ s in Set.Ioi r, (1 + δ s) * s ^ (-(M.d : ℝ) - M.α - 1) := by
    rw [M.K_eq_integral r hr]
    exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => hδ s (lt_trans hr hs))
  have hsub : ∫ s in Set.Ioi r, (1 + δ s) * s ^ (-(M.d : ℝ) - M.α - 1)
      = r * ∫ t in Set.Ioi (1 : ℝ),
          (1 + δ (r * t)) * (r * t) ^ (-(M.d : ℝ) - M.α - 1) := by
    have h := integral_comp_mul_left_Ioi' (g := fun s : ℝ =>
      (1 + δ s) * s ^ (-(M.d : ℝ) - M.α - 1)) (a := (1 : ℝ)) (b := r) hr
    rw [mul_one, smul_eq_mul] at h
    exact h.symm
  have hfac : ∀ t ∈ Set.Ioi (1 : ℝ),
      (1 + δ (r * t)) * (r * t) ^ (-(M.d : ℝ) - M.α - 1)
        = r ^ (-(M.d : ℝ) - M.α - 1)
            * ((1 + δ (r * t)) * t ^ (-(M.d : ℝ) - M.α - 1)) := by
    intro t ht
    have htpos : 0 < t := lt_trans one_pos ht
    rw [Real.mul_rpow hr.le htpos.le]
    ring
  have hstep : ∫ t in Set.Ioi (1 : ℝ),
        (1 + δ (r * t)) * (r * t) ^ (-(M.d : ℝ) - M.α - 1)
      = r ^ (-(M.d : ℝ) - M.α - 1)
          * ∫ t in Set.Ioi (1 : ℝ), (1 + δ (r * t)) * t ^ (-(M.d : ℝ) - M.α - 1) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi hfac
  rw [hKr, hsub, hstep]
  generalize hI : (∫ t in Set.Ioi (1 : ℝ),
    (1 + δ (r * t)) * t ^ (-(M.d : ℝ) - M.α - 1)) = I
  have hmul : r ^ (-(M.d : ℝ) - M.α) * r ^ (-1 : ℝ) = r ^ (-(M.d : ℝ) - M.α - 1) := by
    rw [← Real.rpow_add hr]
    rw [show -(M.d : ℝ) - M.α + -1 = -(M.d : ℝ) - M.α - 1 from by ring]
  have h1 : r * r ^ (-(M.d : ℝ) - M.α - 1) = r ^ (-(M.d : ℝ) - M.α) := by
    rw [← hmul, Real.rpow_neg_one]
    field_simp
  have h2 : r ^ ((M.d : ℝ) + M.α) * r ^ (-(M.d : ℝ) - M.α) = 1 := by
    rw [← Real.rpow_add hr]
    have hzero : (M.d : ℝ) + M.α + (-(M.d : ℝ) - M.α) = 0 := by ring
    rw [hzero, Real.rpow_zero]
  calc r * (r ^ (-(M.d : ℝ) - M.α - 1) * I) * r ^ ((M.d : ℝ) + M.α)
      = (r * r ^ (-(M.d : ℝ) - M.α - 1)) * (I * r ^ ((M.d : ℝ) + M.α)) := by ring
    _ = r ^ (-(M.d : ℝ) - M.α) * (I * r ^ ((M.d : ℝ) + M.α)) := by rw [h1]
    _ = I * (r ^ (-(M.d : ℝ) - M.α) * r ^ ((M.d : ℝ) + M.α)) := by ring
    _ = I * (r ^ ((M.d : ℝ) + M.α) * r ^ (-(M.d : ℝ) - M.α)) := by ring
    _ = I * 1 := by rw [h2]
    _ = I := by ring

/-- **Exact asymptotics of the source kernel.**  `K r · r^{d+α} → 1/(d+α)`. -/
theorem tendsto_K_mul_rpow :
    Tendsto (fun r : ℝ => M.K r * r ^ ((M.d : ℝ) + M.α)) atTop
      (𝓝 (1 / ((M.d : ℝ) + M.α))) := by
  obtain ⟨δ, hderiv, hlogerr⟩ := M.exists_error
  simp only [Analysis.IsLogErrorFunction, Analysis.LogarithmicallyIntegrable] at hlogerr
  obtain ⟨⟨hδmeas, -⟩, hδtend⟩ := hlogerr
  have hexp : -(M.d : ℝ) - M.α - 1 < -1 := by linarith [M.hα]
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 hδtend (1 / 2) (by norm_num)
  have hδbd : ∀ s : ℝ, R ≤ s → |δ s| ≤ 1 / 2 := by
    intro s hs
    have h := hR s hs
    rw [Real.dist_eq, sub_zero] at h
    exact le_of_lt h
  have hpowInt : IntegrableOn (fun t : ℝ => t ^ (-(M.d : ℝ) - M.α - 1)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hexp one_pos
  have hval : ∫ t in Set.Ioi (1 : ℝ), (1 + 0) * t ^ (-(M.d : ℝ) - M.α - 1)
      = 1 / ((M.d : ℝ) + M.α) := by
    simp only [add_zero, one_mul]
    rw [integral_Ioi_rpow_of_lt hexp one_pos, Real.one_rpow]
    have hb1 : -(M.d : ℝ) - M.α - 1 + 1 = -((M.d : ℝ) + M.α) := by ring
    rw [hb1]
    field_simp
  have hDCT : Tendsto (fun r : ℝ => ∫ t in Set.Ioi (1 : ℝ),
        (1 + δ (r * t)) * t ^ (-(M.d : ℝ) - M.α - 1)) atTop
      (𝓝 (∫ t in Set.Ioi (1 : ℝ), (1 + 0) * t ^ (-(M.d : ℝ) - M.α - 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (F := fun r t => (1 + δ (r * t)) * t ^ (-(M.d : ℝ) - M.α - 1))
      (f := fun t => (1 + 0) * t ^ (-(M.d : ℝ) - M.α - 1))
      (bound := fun t => 2 * t ^ (-(M.d : ℝ) - M.α - 1))
      (μ := volume.restrict (Set.Ioi (1 : ℝ))) ?_ ?_ ?_ ?_
    · filter_upwards with r
      exact (show Measurable (fun t : ℝ => (1 + δ (r * t)) * t ^ (-(M.d : ℝ) - M.α - 1))
        from by fun_prop).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (max R 0), eventually_gt_atTop (0 : ℝ)] with r hr hrpos
      have hrR : R ≤ r := le_trans (le_max_left _ _) hr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : (0 : ℝ) < t := lt_trans one_pos ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
      have hrt : R ≤ r * t := by nlinarith
      have hδt : |δ (r * t)| ≤ 1 / 2 := hδbd _ hrt
      have hpow : (0 : ℝ) ≤ t ^ (-(M.d : ℝ) - M.α - 1) := Real.rpow_nonneg htpos.le _
      have h1 : |1 + δ (r * t)| ≤ 2 := by
        have h := abs_le.mp hδt
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
      exact mul_le_mul_of_nonneg_right h1 hpow
    · exact hpowInt.const_mul 2
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : (0 : ℝ) < t := lt_trans one_pos ht
      have hrt : Tendsto (fun r : ℝ => r * t) atTop atTop :=
        tendsto_id.atTop_mul_const htpos
      have hcomp : Tendsto (fun r : ℝ => δ (r * t)) atTop (𝓝 0) := hδtend.comp hrt
      exact (tendsto_const_nhds.add hcomp).mul tendsto_const_nhds
  have heq : (fun r : ℝ => M.K r * r ^ ((M.d : ℝ) + M.α))
      =ᶠ[atTop] (fun r : ℝ => ∫ t in Set.Ioi (1 : ℝ),
        (1 + δ (r * t)) * t ^ (-(M.d : ℝ) - M.α - 1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact M.K_mul_rpow_eq_integral δ hderiv hr
  have hlim : Tendsto (fun r : ℝ => ∫ t in Set.Ioi (1 : ℝ),
      (1 + δ (r * t)) * t ^ (-(M.d : ℝ) - M.α - 1)) atTop (𝓝 (1 / ((M.d : ℝ) + M.α))) := by
    rw [← hval]
    exact hDCT
  exact Tendsto.congr' heq.symm hlim

/-- **The source kernel is regularly varying at `∞` of index `-(d+α)`.** -/
theorem K_regularlyVarying :
    Analysis.RegularlyVaryingAtTop M.K (-((M.d : ℝ) + M.α)) := by
  have hcpos : 0 < (M.d : ℝ) + M.α := by
    have h : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
    linarith [M.hα]
  have hmain := M.tendsto_K_mul_rpow
  have hne : (1 / ((M.d : ℝ) + M.α)) ≠ 0 := by
    have : (0 : ℝ) < 1 / ((M.d : ℝ) + M.α) := by positivity
    exact ne_of_gt this
  constructor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ne_of_gt (M.K_pos hx)
  · intro l hl
    have hlpos : (0 : ℝ) < l := hl
    -- the rescaled argument also tends to infinity
    have hlin : Tendsto (fun x : ℝ => l * x) atTop atTop := by
      have h : Tendsto (fun x : ℝ => x * l) atTop atTop := tendsto_id.atTop_mul_const hlpos
      simpa [mul_comm] using h
    have hcomp : Tendsto (fun x : ℝ => M.K (l * x) * (l * x) ^ ((M.d : ℝ) + M.α))
        atTop (𝓝 (1 / ((M.d : ℝ) + M.α))) := hmain.comp hlin
    have hquot : Tendsto (fun x : ℝ =>
        (M.K (l * x) * (l * x) ^ ((M.d : ℝ) + M.α))
          / (M.K x * x ^ ((M.d : ℝ) + M.α))) atTop (𝓝 1) := by
      have h := hcomp.div hmain hne
      rwa [div_self hne] at h
    have hconst : Tendsto (fun x : ℝ => (l ^ ((M.d : ℝ) + M.α))⁻¹) atTop
        (𝓝 ((l ^ ((M.d : ℝ) + M.α))⁻¹)) := tendsto_const_nhds
    have hprod := hquot.mul hconst
    have hprod' : Tendsto (fun x : ℝ => (M.K (l * x) * (l * x) ^ ((M.d : ℝ) + M.α))
          / (M.K x * x ^ ((M.d : ℝ) + M.α)) * (l ^ ((M.d : ℝ) + M.α))⁻¹) atTop
        (𝓝 ((l ^ ((M.d : ℝ) + M.α))⁻¹)) := by
      simpa using hprod
    have hgoal : Tendsto (fun x : ℝ => M.K (l * x) / M.K x) atTop
        (𝓝 ((l ^ ((M.d : ℝ) + M.α))⁻¹)) := by
      refine Tendsto.congr' ?_ hprod'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hlx : (0 : ℝ) < l * x := mul_pos hlpos hx
      have h3 : (l * x) ^ ((M.d : ℝ) + M.α)
          = l ^ ((M.d : ℝ) + M.α) * x ^ ((M.d : ℝ) + M.α) :=
        Real.mul_rpow hlpos.le hx.le
      have hxne : x ^ ((M.d : ℝ) + M.α) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hx _)
      have hlne : l ^ ((M.d : ℝ) + M.α) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hlpos _)
      have h1 : M.K (l * x) ≠ 0 := ne_of_gt (M.K_pos hlx)
      have h2 : M.K x ≠ 0 := ne_of_gt (M.K_pos hx)
      rw [h3]
      field_simp
    have hexp_eq : l ^ (-((M.d : ℝ) + M.α)) = (l ^ ((M.d : ℝ) + M.α))⁻¹ :=
      Real.rpow_neg hlpos.le _
    rw [hexp_eq]
    exact hgoal

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.K_mul_rpow_eq_integral
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_K_mul_rpow
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.K_regularlyVarying
