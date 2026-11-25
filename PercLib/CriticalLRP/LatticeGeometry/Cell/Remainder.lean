/-
# The polynomial remainder in Lemma I.4.6

A direct power-difference estimate gives the `O(r^(d-1))` bound without a
binomial expansion. Constants may depend on the dimension and cube bound.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Scaling

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.LatticeGeometry

open Filter MeasureTheory

open scoped Asymptotics ENNReal Topology

variable {d : ℕ}

/-- The absolute difference between the outer and inner volume powers is at
most an explicit constant times `r ^ (d - 1)` once `0 ≤ C ≤ r`. -/
theorem abs_add_sub_pow_le {C r : ℝ} (hC : 0 ≤ C) (hCr : C ≤ r) :
    |(r + C) ^ d - (r - C) ^ d| ≤
      ((2 : ℝ) * C * (d : ℝ) * (2 : ℝ) ^ (d - 1)) * r ^ (d - 1) := by
  have hr : 0 ≤ r := hC.trans hCr
  have hout : 0 ≤ r + C := by linarith
  have hinner : 0 ≤ r - C := by linarith
  have hbase := abs_pow_sub_pow_le (r + C) (r - C) d
  rw [show r + C - (r - C) = 2 * C by ring, abs_of_nonneg (by positivity : 0 ≤ 2 * C),
    abs_of_nonneg hout, abs_of_nonneg hinner,
    max_eq_left (by linarith : r - C ≤ r + C)] at hbase
  have hpow : (r + C) ^ (d - 1) ≤ (2 * r) ^ (d - 1) :=
    pow_le_pow_left₀ hout (by linarith : r + C ≤ 2 * r) (d - 1)
  calc
    |(r + C) ^ d - (r - C) ^ d| ≤ 2 * C * (d : ℝ) * (r + C) ^ (d - 1) := hbase
    _ ≤ 2 * C * (d : ℝ) * (2 * r) ^ (d - 1) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ((2 : ℝ) * C * (d : ℝ) * (2 : ℝ) ^ (d - 1)) * r ^ (d - 1) := by
      rw [mul_pow]
      ring

/-- The symmetric power-difference remainder has an explicit linear asymptotic
majorant in the next lower power of the radius. -/
theorem isBigOWith_add_sub_pow {C : ℝ} (hC : 0 ≤ C) :
    Asymptotics.IsBigOWith ((2 : ℝ) * C * (d : ℝ) * (2 : ℝ) ^ (d - 1)) atTop
      (fun r : ℝ => (r + C) ^ d - (r - C) ^ d) (fun r => r ^ (d - 1)) := by
  apply Asymptotics.IsBigOWith.of_bound
  filter_upwards [eventually_ge_atTop C, eventually_ge_atTop (1 : ℝ)] with r hCr hr
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hb := abs_add_sub_pow_le (d := d) hC hCr
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 (d - 1))] using hb

/-- The power-difference remainder is `O(r^(d-1))` at infinity. -/
theorem isBigO_add_sub_pow {C : ℝ} (hC : 0 ≤ C) :
    (fun r : ℝ => (r + C) ^ d - (r - C) ^ d) =O[atTop]
      (fun r => r ^ (d - 1)) :=
  (isBigOWith_add_sub_pow hC).isBigO

end PercLib.CriticalLRP.LatticeGeometry
