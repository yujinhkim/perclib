/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Elementary tail estimates for the universal-tightness moment bound

This file collects the elementary real-analysis bounds used to pass from the exponential tail
estimate (I.2.6) of Hutchcroft, arXiv:2508.18807v1 (Theorem I.2.3) to the moment-ratio
inequality of Corollary I.2.5.

The two analytic inputs are Taylor's bound `x^j ≤ 2^j j! e^{x/2}` and the elementary bound
`1 - e^{-u} ≥ u/2` for `0 < u ≤ 1`; the series are summed geometrically in `ℝ≥0∞` using
`ENNReal.tsum_geometric_add_one`.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Tightness

/-! ### Two elementary real bounds -/

/-- `x ^ j ≤ 2 ^ j * j! * exp (x/2)` for `x ≥ 0` (Taylor's theorem at `x/2`). -/
lemma pow_le_two_pow_mul_factorial_exp {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    x ^ j ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (x / 2) := by
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp (x / 2) (by positivity) j
  have h1 : (x / 2) ^ j ≤ (j.factorial : ℝ) * Real.exp (x / 2) := by
    rw [div_le_iff₀ hfac] at h
    linarith
  calc x ^ j = (2 * (x / 2)) ^ j := by ring_nf
    _ = 2 ^ j * (x / 2) ^ j := by rw [mul_pow]
    _ ≤ 2 ^ j * ((j.factorial : ℝ) * Real.exp (x / 2)) := by gcongr
    _ = 2 ^ j * (j.factorial : ℝ) * Real.exp (x / 2) := by ring

/-- `u/2 ≤ 1 - e^{-u}` for `0 < u ≤ 1`. -/
lemma half_le_one_sub_exp_neg {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have hpos : (0 : ℝ) < 1 + u := by linarith
  have hexp : (1 : ℝ) + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h1 : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, show (Real.exp u)⁻¹ = 1 / Real.exp u from by ring]
    exact one_div_le_one_div_of_le hpos hexp
  have h2 : 1 / (1 + u) ≤ 1 - u / 2 := by
    rw [div_le_iff₀ hpos]; nlinarith
  linarith

/-- `x^j * e^{-x} ≤ 2^j j! e^{-x/2}` for `x ≥ 0`. -/
lemma pow_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    x ^ j * Real.exp (-x) ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (-(x / 2)) := by
  have h := pow_le_two_pow_mul_factorial_exp hx j
  have h2 : Real.exp (x / 2) * Real.exp (-x) = Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc x ^ j * Real.exp (-x)
      ≤ (2 ^ j * (j.factorial : ℝ) * Real.exp (x / 2)) * Real.exp (-x) := by gcongr
    _ = 2 ^ j * (j.factorial : ℝ) * (Real.exp (x / 2) * Real.exp (-x)) := by ring
    _ = 2 ^ j * (j.factorial : ℝ) * Real.exp (-(x / 2)) := by rw [h2]

/-! ### The geometric-majorant series bound in `ℝ≥0∞` -/

/-- `∑_{n} e^{-(n+1)c} ≤ 2/c` in `ℝ≥0∞` for `0 < c ≤ 1`. -/
lemma tsum_exp_neg_succ_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))))
      ≤ ENNReal.ofReal (2 / c) := by
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-c)) with hr
  have hterm : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))) = r ^ (n + 1) := by
    intro n
    rw [hr, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hr1 : r ≤ 1 := by
    rw [hr]
    exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hbound : ENNReal.ofReal (c / 2) ≤ 1 - r := by
    rw [hr, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub (p := 1) (q := Real.exp (-c)) (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (half_le_one_sub_exp_neg hc0 hc1)
  have hinv : (1 - r)⁻¹ ≤ ENNReal.ofReal (2 / c) := by
    rw [show ENNReal.ofReal (2 / c) = (ENNReal.ofReal (c / 2))⁻¹ from by
      rw [show (2 : ℝ) / c = (c / 2)⁻¹ from by field_simp]
      exact ENNReal.ofReal_inv_of_pos (by positivity)]
    exact ENNReal.inv_le_inv.mpr hbound
  calc (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))))
      = ∑' n : ℕ, r ^ (n + 1) := by simp only [hterm]
    _ = r * (1 - r)⁻¹ := ENNReal.tsum_geometric_add_one r
    _ ≤ 1 * (1 - r)⁻¹ := by gcongr
    _ = (1 - r)⁻¹ := one_mul _
    _ ≤ ENNReal.ofReal (2 / c) := hinv

/-- `∑_{n} (n+1)^j e^{-(n+1)c} ≤ 2^j j! c^{-j} · (4/c)` in `ℝ≥0∞` for `0 < c ≤ 1`. -/
theorem tsum_pow_mul_exp_neg_succ_le (j : ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ j * ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c)))))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j * (4 / c)) := by
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(c / 2))) with hr
  have hstep : ∀ n : ℕ, (((n : ℝ≥0∞) + 1) ^ j *
        ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) * r ^ (n + 1) := by
    intro n
    have hx : (0 : ℝ) ≤ ((n : ℝ) + 1) * c := by positivity
    have hscal : (((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c)))
        ≤ (2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j * Real.exp (-(((n : ℝ) + 1) * c / 2)) := by
      have h1 := pow_mul_exp_neg_le hx j
      have hcpos : (0 : ℝ) < c ^ j := by positivity
      have h3 : (((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c)))
          ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (-(((n : ℝ) + 1) * c / 2)) / c ^ j := by
        rw [le_div_iff₀ hcpos]
        calc ((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c)) * c ^ j
            = (((n : ℝ) + 1) * c) ^ j * Real.exp (-(((n : ℝ) + 1) * c)) := by
              rw [mul_pow]; ring
          _ ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (-(((n : ℝ) + 1) * c / 2)) := h1
      calc ((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c))
          ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (-(((n : ℝ) + 1) * c / 2)) / c ^ j := h3
        _ = 2 ^ j * (j.factorial : ℝ) * c⁻¹ ^ j
              * Real.exp (-(((n : ℝ) + 1) * c / 2)) := by
            rw [inv_pow, div_eq_mul_inv]
            ring
    have hcastR : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast]
      norm_num
    have hcast : (((n : ℝ≥0∞) + 1) ^ j * ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))))
        = ENNReal.ofReal (((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), hcastR]
    rw [hcast]
    calc ENNReal.ofReal (((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c)))
        ≤ ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j
            * Real.exp (-(((n : ℝ) + 1) * c / 2))) := ENNReal.ofReal_le_ofReal hscal
      _ = ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) * r ^ (n + 1) := by
          rw [hr, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
            ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
  calc (∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ j * ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c)))))
      ≤ ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) * r ^ (n + 1) :=
        ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) *
          ∑' n : ℕ, r ^ (n + 1) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) * ENNReal.ofReal (4 / c) := by
        have hgeom : (∑' n : ℕ, r ^ (n + 1))
            = ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * (c / 2)))) := by
          refine tsum_congr fun n => ?_
          rw [hr, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        rw [hgeom]
        have hhalf := tsum_exp_neg_succ_le (c := c / 2) (by positivity) (by linarith)
        rw [show (2 : ℝ) / (c / 2) = 4 / c from by field_simp; norm_num] at hhalf
        exact mul_le_mul_right hhalf _
    _ = ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j * (4 / c)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]

end PercLib.CriticalLRP.Tightness
