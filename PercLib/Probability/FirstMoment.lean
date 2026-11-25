/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 135 (Q-14), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import PercLib.Probability.Cylinder

/-!
# First moments of the number of open indices

The expected number of open indices in a finite set `F` is `∑ i ∈ F, p i`, for every
profile and every index type. The cardinality of any set, coerced to `ℝ≥0∞`, is the sum of
its indicator (`encard_eq_tsum_indicator`), which turns expected counts into sums of
probabilities. This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {ι : Type*}

/-- The cardinality of a set, in `ℝ≥0∞`, is the sum of its indicator. -/
theorem encard_eq_tsum_indicator {α : Type*} (S : Set α) :
    (S.encard : ℝ≥0∞) = ∑' a, S.indicator (fun _ => (1 : ℝ≥0∞)) a := by
  rw [← ENNReal.tsum_set_one, tsum_subtype S (fun _ => (1 : ℝ≥0∞))]

/-- The number of open indices in a finite set is the sum of the open indicators. -/
theorem ncard_inter_finset_eq_sum (F : Finset ι) (ω : Set ι) :
    ((ω ∩ F).ncard : ℝ≥0∞) =
      ∑ i ∈ F, {ω' : Set ι | i ∈ ω'}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  have h : ω ∩ (F : Set ι) = ((F.filter (· ∈ ω) : Finset ι) : Set ι) := by
    ext i; simp [and_comm]
  rw [h, ncard_coe_finset, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ ω <;> simp [hi]

/-- **Expected number of open indices in a finite set.** Any index type, any profile. -/
theorem lintegral_ncard_inter_finset (p : ι → unitInterval) (F : Finset ι) :
    ∫⁻ ω, ((ω ∩ F).ncard : ℝ≥0∞) ∂prodBernoulli p =
      ∑ i ∈ F, (unitInterval.toNNReal (p i) : ℝ≥0∞) := by
  simp_rw [ncard_inter_finset_eq_sum F]
  rw [lintegral_finsetSum _ fun i _ => measurable_const.indicator (measurableSet_mem i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_indicator_const (measurableSet_mem i), one_mul, prodBernoulli_setOf_mem]

/-! ### Non-vacuity -/

/-- Two open indices out of two, with probabilities `0` and `1`. -/
example : ∫⁻ ω, ((ω ∩ (Finset.univ : Finset Bool)).ncard : ℝ≥0∞)
    ∂prodBernoulli (fun b : Bool => if b then (1 : unitInterval) else 0) = 1 := by
  rw [lintegral_ncard_inter_finset, Fintype.sum_bool]
  simp

end PercLib.Probability
