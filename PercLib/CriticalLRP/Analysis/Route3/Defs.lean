/- Integrated from independently rebuilt Ultramath work.
Production base 37c0efc68ae8ef365d8d155bc931fd784fdfde2b.
Scratch source: ../../.ultramath/smwvnrt0i/m2/Defs.lean.
-/

module

public import Mathlib

/-!
# Definitions: the tail envelope, the truncation scale, the ratio constant

All three are `Prop`-free data.  The only facts recorded here are the elementary sign and
size properties used by `Main.lean`: the envelope is nonnegative, the ratio constant is
positive, and the truncation scale is at least `1` and lies between `m^{2/3}` and
`m^{2/3}+1` as soon as `m ≥ 1`.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Analysis.Route3

/-- The `n^{-1/2}` volume-tail envelope `C / √n` of the source's triangle-condition input
(`P_{β_c}(|K| ≥ n) ⪯ n^{-1/2}`), as an extended nonnegative real. -/
noncomputable def tailEnvelope (C : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (C / Real.sqrt n)

/-- The optimizing truncation scale `⌈m^{2/3}⌉` of the source's optimization
`N = ⌈(E_{β_c,r}|K|^2)^{2/3}⌉`, written as the ceiling of `m^{1/3} · m^{1/3}` so that the
ceiling is taken of a nonnegative real for `m ≥ 0`. -/
noncomputable def cutoffScale (m : ℝ) : ℕ :=
  ⌈m ^ ((1 : ℝ) / 3) * m ^ ((1 : ℝ) / 3)⌉₊

/-- The constant `K` of the inequality `(∫⁻ X)^3 ≤ K · ∫⁻ X^2` produced by the optimization:
`(4C + 1)^3` for a tail envelope with constant `C`. -/
noncomputable def ratioConst (C : ℝ) : ℝ :=
  (4 * C + 1) ^ 3

theorem tailEnvelope_nonneg (C : ℝ) (n : ℕ) : 0 ≤ tailEnvelope C n :=
  zero_le

theorem tailEnvelope_zero (C : ℝ) : tailEnvelope C 0 = 0 := by
  simp [tailEnvelope]

theorem tailEnvelope_eq_ofReal {C : ℝ} {n : ℕ} (hn : 0 < n) :
    tailEnvelope C n = ENNReal.ofReal C / ENNReal.ofReal (Real.sqrt n) := by
  rw [tailEnvelope, ENNReal.ofReal_div_of_pos (Real.sqrt_pos.2 (by exact_mod_cast hn))]

theorem ratioConst_pos {C : ℝ} (hC : 0 ≤ C) : 0 < ratioConst C := by
  have : 0 < 4 * C + 1 := by linarith
  simpa [ratioConst] using pow_pos this 3

theorem ratioConst_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ ratioConst C :=
  (ratioConst_pos hC).le

theorem ratioConst_ne_zero {C : ℝ} (hC : 0 ≤ C) : ratioConst C ≠ 0 :=
  (ratioConst_pos hC).ne'

/-- The truncation scale is at least `1` as soon as `m ≥ 1`: the `N ≥ 1` side condition of
the source's optimization is a theorem, not an extra hypothesis. -/
theorem one_le_cutoffScale {m : ℝ} (hm : 1 ≤ m) : 1 ≤ cutoffScale m := by
  have ht1 : 1 ≤ m ^ ((1 : ℝ) / 3) := Real.one_le_rpow hm (by norm_num)
  have hle : (1 : ℝ) ≤ m ^ ((1 : ℝ) / 3) * m ^ ((1 : ℝ) / 3) := by nlinarith
  have := Nat.le_ceil (m ^ ((1 : ℝ) / 3) * m ^ ((1 : ℝ) / 3))
  have : (1 : ℝ) ≤ (cutoffScale m : ℝ) := le_trans hle this
  exact_mod_cast this

/-- Lower bound on the truncation scale: `m^{2/3} ≤ ⌈m^{2/3}⌉`. -/
theorem cutoffScale_ge {m : ℝ} (_hm : 0 ≤ m) :
    m ^ ((1 : ℝ) / 3) * m ^ ((1 : ℝ) / 3) ≤ (cutoffScale m : ℝ) :=
  Nat.le_ceil _

/-- Upper bound on the truncation scale: `⌈m^{2/3}⌉ < m^{2/3} + 1`. -/
theorem cutoffScale_lt {m : ℝ} (hm : 0 ≤ m) :
    (cutoffScale m : ℝ) < m ^ ((1 : ℝ) / 3) * m ^ ((1 : ℝ) / 3) + 1 := by
  have ht0 : (0 : ℝ) ≤ m ^ ((1 : ℝ) / 3) * m ^ ((1 : ℝ) / 3) := by
    have := Real.rpow_nonneg hm ((1 : ℝ) / 3); nlinarith
  exact Nat.ceil_lt_add_one ht0

/-- `m^{2/3}` is the cube of `m^{1/3}`. -/
theorem rpow_third_sq (m : ℝ) :
    m ^ ((1 : ℝ) / 3) * m ^ ((1 : ℝ) / 3) = (m ^ ((1 : ℝ) / 3)) ^ 2 := by ring

/-- `(m^{1/3})^3 = m` for `m ≥ 0`. -/
theorem rpow_third_cube {m : ℝ} (hm : 0 ≤ m) : (m ^ ((1 : ℝ) / 3)) ^ 3 = m := by
  have := Real.rpow_inv_natCast_pow (x := m) (n := 3) hm (by norm_num)
  rw [show ((3 : ℕ) : ℝ)⁻¹ = (1 : ℝ) / 3 by norm_num] at this
  exact this

end PercLib.CriticalLRP.Analysis.Route3
