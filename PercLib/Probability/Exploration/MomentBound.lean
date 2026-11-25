/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Pointwise transfer of an exponential growth bound to polynomial moments.

Accepted from independent submission `smwp9xgrt` direction D2.
These are finite-configuration and scalar ingredients, not an infinite-volume
cluster-moment theorem.  The adapted-revelation and exploration bridges remain open.
-/
module

/-
`PROOF.md` Lemma 6.1 and §2: passage from a uniform exponential moment bound
`E[λ^{|K_o|}] ≤ 1/m` to uniform all-order moment bounds, with the explicit constant
`k! / (m (log λ)^k)`.

The probability is *not* formalized here: `PROOF.md` Theorem 1 (`E[λ^{|K_o|}] ≤ 1/m`) is the
missing probabilistic input; this file compiles everything downstream of it.
-/
public import PercLib.Probability.Exploration.Envelope.Defs
public import PercLib.Probability.Exploration.Envelope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

@[expose] public section

open PercLib.Probability.ExplorationEnvelope

namespace PercLib.Probability.ExplorationEnvelope

variable {m : ℝ}

/-- **`PROOF.md` Lemma 6.1 (moment transfer, pointwise).** For `λ > 1`, `x ≥ 0` and `k ∈ ℕ`:
`x^k ≤ (k! / (log λ)^k) λ^x`. Applied to `x = |K_o|` and integrated against `P` this turns
`E[λ^{|K_o|}] ≤ C` into `E[|K_o|^k] ≤ C k! / (log λ)^k`. -/
theorem pow_le_factorial_div_log_mul_rpow {lam : ℝ} (hlam : 1 < lam) (k : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    x ^ k ≤ ((k.factorial : ℝ) / (Real.log lam) ^ k) * lam ^ x := by
  have hc : 0 < Real.log lam := Real.log_pos hlam
  have hmem : Real.exp (Real.log lam * x) = lam ^ x := by
    rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < lam)]
  have hfac : (0:ℝ) < (k.factorial : ℝ) := by positivity
  have h1 : (Real.log lam * x) ^ k / (k.factorial : ℝ)
      ≤ Real.exp (Real.log lam * x) :=
    Real.pow_div_factorial_le_exp (x := Real.log lam * x) (by positivity) k
  have h2 : (Real.log lam * x) ^ k ≤ (k.factorial : ℝ) * Real.exp (Real.log lam * x) := by
    rw [div_le_iff₀ hfac] at h1
    linarith
  rw [hmem, mul_pow] at h2
  have hck : (0:ℝ) < (Real.log lam) ^ k := pow_pos hc k
  have h4 : x ^ k ≤ ((k.factorial : ℝ) * lam ^ x) / (Real.log lam) ^ k := by
    rw [le_div_iff₀ hck]
    linarith [h2]
  calc x ^ k ≤ ((k.factorial : ℝ) * lam ^ x) / (Real.log lam) ^ k := h4
    _ = ((k.factorial : ℝ) / (Real.log lam) ^ k) * lam ^ x := by ring

/-- **`PROOF.md` §2, Theorem 2, scalar content.** For `0 < m < 1` and every `k` there is `λ > 1`
with `m λ ≤ e^{m-1}` (so that Theorem 1 applies) and
`∀ x ≥ 0, x^k ≤ (k! / (m (log λ)^k)) λ^x`.
Consequently `E[|K_o|^k] ≤ k! / (m (log λ)^k)` for every root `o`, uniformly in `o`, once
`E[λ^{|K_o|}] ≤ 1/m` (Theorem 1) is available. -/
theorem exists_lambda_and_moment_bound (hm : 0 < m) (hm1 : m < 1) (k : ℕ) :
    ∃ lam : ℝ, 1 < lam ∧ m * lam ≤ Real.exp (m - 1) ∧
      ∀ x : ℝ, 0 ≤ x →
        x ^ k ≤ ((k.factorial : ℝ) / (m * (Real.log lam) ^ k)) * lam ^ x := by
  obtain ⟨lam, h1, h2⟩ := exists_admissible_lambda hm hm1
  refine ⟨lam, h1, h2, fun x hx => ?_⟩
  have hbasic := pow_le_factorial_div_log_mul_rpow h1 k hx
  have hfac0 : (0:ℝ) ≤ (k.factorial : ℝ) / (Real.log lam) ^ k := by
    have : (0:ℝ) < (Real.log lam) ^ k := pow_pos (Real.log_pos h1) k
    positivity
  have hminv : (1:ℝ) ≤ m⁻¹ := by
    have := one_div_le_one_div_of_le hm hm1.le
    simpa using this
  have hstep : (k.factorial : ℝ) / (Real.log lam) ^ k
      ≤ ((k.factorial : ℝ) / (Real.log lam) ^ k) * m⁻¹ :=
    le_mul_of_one_le_right hfac0 hminv
  have hconst : ((k.factorial : ℝ) / (Real.log lam) ^ k) * m⁻¹
      = (k.factorial : ℝ) / (m * (Real.log lam) ^ k) := by
    field_simp
  have hpow : (0:ℝ) ≤ lam ^ x := (Real.rpow_pos_of_pos (by linarith) x).le
  have hmain : ((k.factorial : ℝ) / (Real.log lam) ^ k) * lam ^ x
      ≤ ((k.factorial : ℝ) / (m * (Real.log lam) ^ k)) * lam ^ x := by
    rw [← hconst]
    exact mul_le_mul_of_nonneg_right hstep hpow
  exact le_trans hbasic hmain

end PercLib.Probability.ExplorationEnvelope
