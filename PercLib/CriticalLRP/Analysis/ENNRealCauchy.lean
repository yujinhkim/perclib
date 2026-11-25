/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

public import Mathlib.Analysis.MeanInequalities

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.Analysis

open scoped ENNReal

/-- Cauchy--Schwarz for finite sums of nonnegative extended reals, written
with half powers so that infinite sums require no finiteness hypothesis. -/
theorem sum_rpow_half_mul_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0∞) :
    ∑ i ∈ s, (f i * g i) ^ (1 / 2 : ℝ) ≤
      (∑ i ∈ s, f i) ^ (1 / 2 : ℝ) * (∑ i ∈ s, g i) ^ (1 / 2 : ℝ) := by
  have hs (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have h := ENNReal.inner_le_Lp_mul_Lq (s := s)
    (fun i => (f i) ^ (1 / 2 : ℝ)) (fun i => (g i) ^ (1 / 2 : ℝ))
    Real.HolderConjugate.two_two
  calc
    ∑ i ∈ s, (f i * g i) ^ (1 / 2 : ℝ) =
        ∑ i ∈ s, (f i) ^ (1 / 2 : ℝ) * (g i) ^ (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ _ := by simpa only [hs] using h

/-- Cauchy--Schwarz for arbitrary sums of nonnegative extended reals,
including infinite sums. -/
theorem tsum_rpow_half_mul_le {ι : Type*} (f g : ι → ℝ≥0∞) :
    ∑' i, (f i * g i) ^ (1 / 2 : ℝ) ≤
      (∑' i, f i) ^ (1 / 2 : ℝ) * (∑' i, g i) ^ (1 / 2 : ℝ) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => (sum_rpow_half_mul_le s f g).trans ?_
  gcongr
  · exact ENNReal.sum_le_tsum s
  · exact ENNReal.sum_le_tsum s

end PercLib.CriticalLRP.Analysis
