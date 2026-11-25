/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The scalar branching-envelope recursion and admissible exponential parameters.

Accepted from independent submission `smwp9xgrt` direction D2.
These are finite-configuration and scalar ingredients, not an infinite-volume
cluster-moment theorem.  The adapted-revelation and exploration bridges remain open.
-/
module

/-
The scalar envelope recursion of `PROOF.md` §5: monotonicity, the explicit upper bound
`u_n ≤ 1/(m λ)` under `m λ ≤ e^{m-1}`, and existence of an admissible `λ > 1`.

All statements are real analysis; no probability. See `PROOF.md` Lemma 5.1, 5.2 and §2.
-/
public import PercLib.Probability.Exploration.Envelope.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

@[expose] public section

open PercLib.Probability.ExplorationEnvelope

namespace PercLib.Probability.ExplorationEnvelope

variable {m lam : ℝ}

/-- `PROOF.md` Lemma 5.1 (lower half): every envelope entry is at least `1`. -/
theorem one_le_envelope (hm : 0 ≤ m) (hlam : 1 ≤ lam) (n : ℕ) : 1 ≤ envelope m lam n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [envelope_succ, envelopeStep]
    refine Real.one_le_exp ?_
    have h1 : (1:ℝ) ≤ lam * envelope m lam n := by
      simpa using mul_le_mul hlam ih (by norm_num) (by linarith)
    exact mul_nonneg hm (by linarith)

/-- `PROOF.md` Lemma 5.1: the envelope sequence is nondecreasing. -/
theorem envelope_le_succ (hm : 0 ≤ m) (hlam : 1 ≤ lam) (n : ℕ) :
    envelope m lam n ≤ envelope m lam (n + 1) := by
  induction n with
  | zero =>
    rw [envelope_zero, envelope_succ, envelopeStep, envelope_zero]
    refine Real.one_le_exp ?_
    have h1 : (1:ℝ) ≤ lam * 1 := by simpa using hlam
    exact mul_nonneg hm (by linarith)
  | succ n ih =>
    rw [envelope_succ, envelope_succ, envelopeStep, envelopeStep]
    refine Real.exp_le_exp.mpr ?_
    have h2 : lam * envelope m lam n ≤ lam * envelope m lam (n + 1) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    exact mul_le_mul_of_nonneg_left (by linarith) hm

/-- `PROOF.md` Lemma 5.1: the envelope sequence is monotone. -/
theorem envelope_monotone (hm : 0 ≤ m) (hlam : 1 ≤ lam) : Monotone (envelope m lam) :=
  monotone_nat_of_le_succ (envelope_le_succ hm hlam)

/-- The induction used in `PROOF.md` Proposition 5.3 and Lemma 5.2: any `u ≥ 1` fixed by one step
of the recursion bounds the whole envelope sequence. -/
theorem envelope_le_of_step_le (hm : 0 ≤ m) (hlam : 1 ≤ lam) {u : ℝ} (hu : 1 ≤ u)
    (hstep : envelopeStep m lam u ≤ u) (n : ℕ) : envelope m lam n ≤ u := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [envelope_succ, envelopeStep]
    refine le_trans (Real.exp_le_exp.mpr ?_) hstep
    have h2 : lam * envelope m lam n ≤ lam * u :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    exact mul_le_mul_of_nonneg_left (by linarith) hm

/-- `PROOF.md` Lemma 5.2: for `0 < m ≤ 1`, `1 ≤ λ` and `m λ ≤ e^{m-1}`, the explicit candidate
`u = 1/(m λ)` is a supersolution of the recursion, hence bounds the whole sequence. -/
theorem envelope_le_inv_mul (hm : 0 < m) (hm1 : m ≤ 1) (hlam : 1 ≤ lam)
    (hcond : m * lam ≤ Real.exp (m - 1)) (n : ℕ) :
    envelope m lam n ≤ 1 / (m * lam) := by
  have hmpos : (0:ℝ) < m * lam := by nlinarith
  have hle1 : m * lam ≤ 1 := by
    have h2 : Real.exp (m - 1) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    linarith
  refine envelope_le_of_step_le hm.le hlam ?_ ?_ n
  · have h := one_div_le_one_div_of_le hmpos hle1
    rwa [one_div_one] at h
  · rw [envelopeStep]
    have harg : m * (lam * (1 / (m * lam)) - 1) = 1 - m := by field_simp
    rw [harg]
    have he : Real.exp (1 - m) = 1 / Real.exp (m - 1) := by
      rw [show (1:ℝ) - m = -(m - 1) by ring, Real.exp_neg, one_div]
    rw [he]
    exact one_div_le_one_div_of_le hmpos hcond

/-- For `0 < m < 1` there is `λ > 1` with `m λ ≤ e^{m-1}`, so the hypothesis of `PROOF.md`
Theorem 1 with `λ > 1` is satisfiable. -/
theorem exists_admissible_lambda (hm : 0 < m) (hm1 : m < 1) :
    ∃ lam : ℝ, 1 < lam ∧ m * lam ≤ Real.exp (m - 1) := by
  have hmlog : Real.log m < m - 1 := Real.log_lt_sub_one_of_pos hm (ne_of_lt hm1)
  have hmexp : m < Real.exp (m - 1) := by
    calc m = Real.exp (Real.log m) := (Real.exp_log hm).symm
      _ < Real.exp (m - 1) := Real.exp_lt_exp.mpr hmlog
  refine ⟨(1 + Real.exp (m - 1) / m) / 2, ?_, ?_⟩
  · have : 1 < Real.exp (m - 1) / m := by rw [lt_div_iff₀ hm]; linarith
    linarith
  · have hkey : Real.exp (m - 1) / m * m = Real.exp (m - 1) := by field_simp
    nlinarith

end PercLib.Probability.ExplorationEnvelope
