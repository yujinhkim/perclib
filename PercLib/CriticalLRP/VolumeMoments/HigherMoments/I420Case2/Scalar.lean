/- Integrated from independently rebuilt Ultramath work.
Production base e6fb888fa60f4bb3d7fa5ab717b2d149345e3a7f.
Scratch source: repository-root .ultramath/smwwp7q3k/m1/.
-/

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The scalar asymptotic comparison of Proposition I.4.20, Case 2 (`d = 3α`):  the Cauchy–Schwarz
bound `√(C (M₂/M₁)^{2p+1} M₁) √(M_r M₁)` is
`≤ (√(Cγ³)A⁴/(cA'²)) √ε · |B_r| (M₂/M₁)^{p-1} M₁²`
whenever `M₂/M₁ ≤ γ M₁²`, `A' r^α ≤ M₁ ≤ A r^α`, `M_r ≤ ε r^{(d+α)/2}`,
`|B_r| ≥ c r^d` and
`3α ≤ d`.  This is the exact algebraic content of the last display of Case 2.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case2.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

noncomputable section

open Filter Topology Set
open scoped ENNReal NNReal Topology Asymptotics

namespace PercLib.CriticalLRP.Analysis.I420Case2

/-- `(x r^α)^n = x^n r^{nα}` for `r > 0`. -/
theorem mul_rpow_pow {r α x : ℝ} (hr : 0 < r) (n : ℕ) :
    (x * r ^ α) ^ n = x ^ n * r ^ ((n : ℝ) * α) := by
  have h1 : (r ^ α) ^ n = r ^ ((n : ℝ) * α) := by
    rw [← Real.rpow_natCast (r ^ α) n, ← Real.rpow_mul (le_of_lt hr) α (n : ℝ), mul_comm]
  rw [mul_pow, h1]

/-- The scalar comparison behind Case 2 of Proposition I.4.20. -/
theorem sqrt_bound_le {α d C γ A A' c ε b s m Mr r : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (h3 : 3 * α ≤ d) (hr : 1 ≤ r)
    (hC : 0 ≤ C) (hγ : 0 ≤ γ) (_hA : 0 ≤ A) (hA' : 0 < A') (hc : 0 < c) (hε : 0 ≤ ε)
    (hs : 0 ≤ s) (hm : 0 < m) (hMr : 0 ≤ Mr)
    (hsq : s ≤ γ * m ^ 2) (hmhi : m ≤ A * r ^ α) (hmlo : A' * r ^ α ≤ m)
    (hMrb : Mr ≤ ε * r ^ ((d + α) / 2)) (hb : c * r ^ d ≤ b) :
    Real.sqrt (C * s ^ (2 * p + 1) * m) * Real.sqrt (Mr * m)
      ≤ (Real.sqrt (C * γ ^ 3) * A ^ 4 / (c * A' ^ 2)) * Real.sqrt ε
          * (b * s ^ (p - 1) * m ^ 2) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hm0 : (0 : ℝ) ≤ m := le_of_lt hm
  set K : ℝ := Real.sqrt (C * γ ^ 3) * A ^ 4 / (c * A' ^ 2) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    positivity
  -- the constant identity
  have hKsq : K ^ 2 = C * γ ^ 3 * A ^ 8 / (c ^ 2 * A' ^ 4) := by
    rw [hK, div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  -- bound `s³ ≤ γ³ m⁶`
  have hcube : s ^ 3 ≤ γ ^ 3 * m ^ 6 := by
    have := pow_le_pow_left₀ hs hsq 3
    calc s ^ 3 ≤ (γ * m ^ 2) ^ 3 := this
      _ = γ ^ 3 * m ^ 6 := by ring
  -- `A'^4 r^{4α} ≤ m^4`
  have hm4 : A' ^ 4 * r ^ ((4 : ℝ) * α) ≤ m ^ 4 := by
    refine le_trans (le_of_eq ?_)
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ A' * r ^ α) hmlo 4)
    rw [mul_rpow_pow hr0 4]
    norm_num
  -- `m^8 ≤ A^8 r^{8α}`
  have hm8 : m ^ 8 ≤ A ^ 8 * r ^ ((8 : ℝ) * α) :=
    le_trans (pow_le_pow_left₀ hm0 hmhi 8) (le_of_eq (mul_rpow_pow hr0 8))
  -- `c² r^{2d} ≤ b²`
  have hb2 : c ^ 2 * r ^ ((2 : ℝ) * d) ≤ b ^ 2 := by
    refine le_trans (le_of_eq ?_)
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ c * r ^ d) hb 2)
    rw [mul_rpow_pow hr0 2]
    norm_num
  -- the exponent comparison `r^{8α + (d+α)/2} ≤ r^{2d + 4α}`
  have hexp : r ^ ((8 : ℝ) * α + (d + α) / 2) ≤ r ^ ((2 : ℝ) * d + (4 : ℝ) * α) :=
    Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  -- core inequality (after cancelling `(s^{p-1})²`)
  -- expansion helpers (always expand the summed exponent with `Real.rpow_add`)
  have hexp8 : C * γ ^ 3 * A ^ 8 * ε * r ^ ((8 : ℝ) * α + (d + α) / 2)
      = C * γ ^ 3 * A ^ 8 * r ^ ((8 : ℝ) * α) * (ε * r ^ ((d + α) / 2)) := by
    rw [Real.rpow_add hr0]
    ring
  have hexp24 : C * γ ^ 3 * A ^ 8 * ε * r ^ ((2 : ℝ) * d + (4 : ℝ) * α)
      = C * γ ^ 3 * A ^ 8 * ε * (r ^ ((2 : ℝ) * d) * r ^ ((4 : ℝ) * α)) := by
    rw [Real.rpow_add hr0]
  have hcore : C * s ^ 3 * m ^ 2 * Mr ≤ K ^ 2 * ε * b ^ 2 * m ^ 4 := by
    have h1 : C * s ^ 3 * m ^ 2 ≤ C * γ ^ 3 * m ^ 8 := by
      have a1 : C * s ^ 3 ≤ C * (γ ^ 3 * m ^ 6) := mul_le_mul_of_nonneg_left hcube hC
      nlinarith [a1, mul_le_mul_of_nonneg_right a1 (le_of_lt hm),
        (by positivity : (0 : ℝ) ≤ m ^ 2)]
    have h2 : C * s ^ 3 * m ^ 2 * Mr
        ≤ C * γ ^ 3 * m ^ 8 * (ε * r ^ ((d + α) / 2)) := by
      have hh := mul_le_mul h1 hMrb hMr (by positivity : (0 : ℝ) ≤ C * γ ^ 3 * m ^ 8)
      nlinarith [hh]
    have h3 : C * γ ^ 3 * m ^ 8 ≤ C * γ ^ 3 * A ^ 8 * r ^ ((8 : ℝ) * α) := by
      have hh := mul_le_mul_of_nonneg_left hm8 (by positivity : (0 : ℝ) ≤ C * γ ^ 3)
      nlinarith [hh]
    have hstep1 : C * s ^ 3 * m ^ 2 * Mr
        ≤ C * γ ^ 3 * A ^ 8 * ε * r ^ ((8 : ℝ) * α + (d + α) / 2) := by
      refine le_trans h2 ?_
      rw [hexp8]
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    have hstep2 : C * γ ^ 3 * A ^ 8 * ε * r ^ ((8 : ℝ) * α + (d + α) / 2)
        ≤ C * γ ^ 3 * A ^ 8 * ε * r ^ ((2 : ℝ) * d + (4 : ℝ) * α) := by
      gcongr
    have hstep3 : C * γ ^ 3 * A ^ 8 * ε * r ^ ((2 : ℝ) * d + (4 : ℝ) * α)
        ≤ K ^ 2 * ε * b ^ 2 * m ^ 4 := by
      have hD : (0 : ℝ) < c ^ 2 * A' ^ 4 := by positivity
      have hND : K ^ 2 * ε * b ^ 2 * m ^ 4
          = (C * γ ^ 3 * A ^ 8 * ε * b ^ 2 * m ^ 4) / (c ^ 2 * A' ^ 4) := by
        rw [hKsq, div_eq_mul_inv]
        ring
      rw [hND, le_div_iff₀ hD, hexp24]
      have e2 : c ^ 2 * r ^ ((2 : ℝ) * d) * (A' ^ 4 * r ^ ((4 : ℝ) * α)) ≤ b ^ 2 * m ^ 4 :=
        mul_le_mul hb2 hm4 (mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt hr0) _))
          (sq_nonneg b)
      have e4 : c ^ 2 * r ^ ((2 : ℝ) * d) * (A' ^ 4 * r ^ ((4 : ℝ) * α))
          = (r ^ ((2 : ℝ) * d) * r ^ ((4 : ℝ) * α)) * (c ^ 2 * A' ^ 4) := by ring
      rw [e4] at e2
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left e2
        (by positivity : (0 : ℝ) ≤ C * γ ^ 3 * A ^ 8 * ε)
    exact le_trans hstep1 (le_trans hstep2 hstep3)
  -- assemble the square roots
  have hsp : s ^ (2 * p + 1) = s ^ (2 * p - 2) * s ^ 3 := by
    rw [← pow_add]
    congr 1
    omega
  have hsqp : s ^ (2 * p - 2) = s ^ (p - 1) * s ^ (p - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : (C * s ^ (2 * p + 1) * m) * (Mr * m)
      ≤ ((K * Real.sqrt ε) * (b * s ^ (p - 1) * m ^ 2)) ^ 2 := by
    calc (C * s ^ (2 * p + 1) * m) * (Mr * m)
        = s ^ (2 * p - 2) * (C * s ^ 3 * m ^ 2 * Mr) := by
          rw [hsp]
          ring
      _ ≤ s ^ (2 * p - 2) * (K ^ 2 * ε * b ^ 2 * m ^ 4) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = ((K * Real.sqrt ε) * (b * s ^ (p - 1) * m ^ 2)) ^ 2 := by
          rw [hsqp, mul_pow, mul_pow, Real.sq_sqrt hε]
          ring
  have hA0 : (0 : ℝ) ≤ C * s ^ (2 * p + 1) * m := by positivity
  have hb0 : (0 : ℝ) ≤ b := le_trans (by positivity) hb
  calc Real.sqrt (C * s ^ (2 * p + 1) * m) * Real.sqrt (Mr * m)
      = Real.sqrt ((C * s ^ (2 * p + 1) * m) * (Mr * m)) :=
        (Real.sqrt_mul (x := C * s ^ (2 * p + 1) * m) (y := Mr * m) hA0).symm
    _ ≤ Real.sqrt (((K * Real.sqrt ε) * (b * s ^ (p - 1) * m ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = (Real.sqrt (C * γ ^ 3) * A ^ 4 / (c * A' ^ 2)) * Real.sqrt ε
          * (b * s ^ (p - 1) * m ^ 2) := by
        rw [Real.sqrt_sq (mul_nonneg (mul_nonneg hK0 (Real.sqrt_nonneg ε))
          (mul_nonneg (mul_nonneg hb0 (by positivity)) (by positivity))), hK]

end PercLib.CriticalLRP.Analysis.I420Case2
