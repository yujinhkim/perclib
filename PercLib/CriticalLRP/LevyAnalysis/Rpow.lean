/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I:
High effective dimension", arXiv:2508.18807v1, Section I.5.2.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.LevyAnalysis.Radial

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The elementary identity `a ^ (-s) = R ^ (-s) + ∫_a^R s t ^ (-s-1) dt` for `0 < a ≤ R`,
in Lebesgue-integral (`ℝ≥0∞`) form. -/
theorem ofReal_rpow_neg_eq_add_lintegral {s R a : ℝ} (hs : 0 < s) (ha : 0 < a) (haR : a ≤ R) :
    ENNReal.ofReal (a ^ (-s))
      = ENNReal.ofReal (R ^ (-s)) + ∫⁻ t in Ioc a R, ENNReal.ofReal (s * t ^ (-s - 1)) := by
  have hcont : ContinuousOn (fun t : ℝ => s * t ^ (-s - 1)) (uIcc a R) := by
    refine ContinuousOn.const_mul ?_ s
    refine ContinuousOn.rpow_const continuousOn_id ?_
    intro t ht
    left
    have : a ≤ t := (uIcc_of_le haR).symm ▸ ht |>.1
    linarith
  have hint : IntervalIntegrable (fun t : ℝ => s * t ^ (-s - 1)) volume a R :=
    hcont.intervalIntegrable
  have hkey : ∫ t in a..R, s * t ^ (-s - 1) = a ^ (-s) - R ^ (-s) := by
    have h0 : (0 : ℝ) ∉ uIcc a R := by
      rw [uIcc_of_le haR]
      simp only [mem_Icc, not_and]
      intro h; linarith
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    have h1 : (-s - 1 + 1 : ℝ) = -s := by ring
    rw [h1, mul_div_assoc']
    field_simp
    ring
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a R)] fun t : ℝ => s * t ^ (-s - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    exact mul_nonneg hs.le (Real.rpow_nonneg ht0.le _)
  have hInt : Integrable (fun t : ℝ => s * t ^ (-s - 1)) (volume.restrict (Ioc a R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le haR).1 hint
  have h1 : ∫⁻ t in Ioc a R, ENNReal.ofReal (s * t ^ (-s - 1))
      = ENNReal.ofReal (a ^ (-s) - R ^ (-s)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le haR]
    exact hkey
  rw [h1, ← ENNReal.ofReal_add (Real.rpow_pos_of_pos (by linarith) (-s)).le (sub_nonneg.2 ?_)]
  · ring_nf
  · calc R ^ (-s) ≤ a ^ (-s) := by
          exact Real.rpow_le_rpow_of_nonpos ha haR (by linarith)

/-- The integral of `x ^ q` over `Ioc 0 R`, as a `ℝ≥0∞`-valued Lebesgue integral. -/
theorem lintegral_Ioc_zero_rpow {q R : ℝ} (hq : -1 < q) (hR : 0 ≤ R) :
    ∫⁻ t in Ioc (0 : ℝ) R, ENNReal.ofReal (t ^ q)
      = ENNReal.ofReal (R ^ (q + 1) / (q + 1)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ q) volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' hq
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) R)] fun t : ℝ => t ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le q
  have hInt : Integrable (fun t : ℝ => t ^ q) (volume.restrict (Ioc (0:ℝ) R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).1 hint
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hR, integral_rpow (Or.inl hq),
    Real.zero_rpow (by linarith : q + 1 ≠ 0), sub_zero]

end PercLib.CriticalLRP.LevyAnalysis
