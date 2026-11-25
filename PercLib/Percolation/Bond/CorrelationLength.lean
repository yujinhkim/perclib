/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 147, Q-20). No upstream proof is copied.
-/
module

public import PercLib.Probability.OpenEventHarris
public import PercLib.Probability.Cylinder
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# The correlation length

`-log τ` is an `EReal`-valued pseudo-distance (Harris). For a translation-invariant two-point
function on an additive group with `τ(0, n v) > 0`, the sequence `a_n = -log τ(0, n v)` is
subadditive, so by Fekete's lemma `a_n / n` converges to `inf_{n ≥ 1} a_n / n`, the inverse
correlation length in the direction `v`; and `τ(0, n v) ≤ exp(-n · inf_m a_m / m)` for every
`n`. No correlation length is defined: the limit is stated explicitly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

/-! ### `-log τ` is a pseudo-distance -/

section Distance

variable {V : Type*}

/-- `-log τ` vanishes on the diagonal. -/
theorem neg_log_tau_self (q : Sym2 V → unitInterval) (x : V) : -ENNReal.log (tau q x x) = 0 := by
  rw [tau_self, ENNReal.log_one, neg_zero]

/-- `-log τ` is symmetric. -/
theorem neg_log_tau_comm (q : Sym2 V → unitInterval) (x y : V) :
    -ENNReal.log (tau q x y) = -ENNReal.log (tau q y x) := by
  rw [tau_comm]

/-- **Triangle inequality** for `-log τ`, with values in `[0, ∞]`. -/
theorem neg_log_tau_le_add [Countable V] (q : Sym2 V → unitInterval) (x y z : V) :
    -ENNReal.log (tau q x z) ≤ -ENNReal.log (tau q x y) + -ENNReal.log (tau q y z) := by
  have h1 : ENNReal.log (tau q x y) ≠ ⊤ := by
    rw [Ne, ENNReal.log_eq_top_iff]; exact ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one _ _ _)
  have h2 : ENNReal.log (tau q y z) ≠ ⊤ := by
    rw [Ne, ENNReal.log_eq_top_iff]; exact ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one _ _ _)
  rw [← sub_eq_add_neg, ← EReal.neg_add (Or.inr h2) (Or.inl h1), EReal.neg_le_neg_iff,
    ← ENNReal.log_mul_add]
  exact ENNReal.log_le_log (tau_mul_tau_le q x y z)

theorem tau_toReal_pos {q : Sym2 V → unitInterval} {x y : V} (h : 0 < tau q x y) :
    0 < (tau q x y).toReal :=
  ENNReal.toReal_pos h.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one _ _ _))

theorem neg_log_tau_nonneg (q : Sym2 V → unitInterval) (x y : V) :
    0 ≤ -Real.log (tau q x y).toReal := by
  rw [neg_nonneg]
  refine Real.log_nonpos ENNReal.toReal_nonneg ?_
  have := ENNReal.toReal_mono ENNReal.one_ne_top (tau_le_one q x y)
  simpa using this

end Distance

/-! ### Fekete's lemma along a direction -/

section Fekete

variable {G : Type*} [AddCommGroup G]

/-- `n ↦ -log τ(0, n v)` is subadditive. -/
theorem subadditive_neg_log_tau [Countable G] (q : Sym2 G → unitInterval) (v : G)
    (hinv : ∀ x y g : G, tau q (x + g) (y + g) = tau q x y)
    (hpos : ∀ n : ℕ, 0 < tau q 0 (n • v)) :
    Subadditive fun n : ℕ => -Real.log (tau q 0 (n • v)).toReal := by
  intro m n
  have hH := tau_mul_tau_le q 0 (m • v) ((m + n) • v)
  have hshift : tau q (m • v) ((m + n) • v) = tau q 0 (n • v) := by
    have := hinv 0 (n • v) (m • v)
    rwa [zero_add, ← add_nsmul, add_comm n m] at this
  rw [hshift] at hH
  have hne : tau q 0 ((m + n) • v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one _ _ _)
  have hr := ENNReal.toReal_mono hne hH
  rw [ENNReal.toReal_mul] at hr
  have hlog := Real.log_le_log (mul_pos (tau_toReal_pos (hpos m)) (tau_toReal_pos (hpos n))) hr
  rw [Real.log_mul (tau_toReal_pos (hpos m)).ne' (tau_toReal_pos (hpos n)).ne'] at hlog
  linarith

theorem bddBelow_neg_log_tau_div (q : Sym2 G → unitInterval) (v : G) :
    BddBelow (range fun n : ℕ => -Real.log (tau q 0 (n • v)).toReal / n) :=
  ⟨0, by
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (neg_log_tau_nonneg q _ _) (Nat.cast_nonneg n)⟩

/-- **Fekete along a direction.** The decay rate of `τ(0, n v)` exists and equals
`inf_{n ≥ 1} -log τ(0, n v) / n`. -/
theorem tendsto_neg_log_tau_div [Countable G] (q : Sym2 G → unitInterval) (v : G)
    (hinv : ∀ x y g : G, tau q (x + g) (y + g) = tau q x y)
    (hpos : ∀ n : ℕ, 0 < tau q 0 (n • v)) :
    Tendsto (fun n : ℕ => -Real.log (tau q 0 (n • v)).toReal / n) atTop
      (nhds (⨅ n : ℕ+, -Real.log (tau q 0 ((n : ℕ) • v)).toReal / n)) := by
  have hsub := subadditive_neg_log_tau q v hinv hpos
  have hbdd := bddBelow_neg_log_tau_div q v
  have hlim : hsub.lim = ⨅ n : ℕ+, -Real.log (tau q 0 ((n : ℕ) • v)).toReal / n := by
    refine le_antisymm ?_ ?_
    · have : Nonempty ℕ+ := ⟨1⟩
      exact le_ciInf fun n => hsub.lim_le_div hbdd n.ne_zero
    · rw [Subadditive.lim]
      refine le_csInf ⟨_, ⟨1, Set.mem_Ici.2 le_rfl, rfl⟩⟩ ?_
      rintro _ ⟨n, hn, rfl⟩
      have hb : BddBelow (range fun n : ℕ+ => -Real.log (tau q 0 ((n : ℕ) • v)).toReal / n) :=
        ⟨0, by
          rintro _ ⟨n, rfl⟩
          exact div_nonneg (neg_log_tau_nonneg q _ _) (Nat.cast_nonneg _)⟩
      exact ciInf_le hb ⟨n, hn⟩
  rw [← hlim]
  exact hsub.tendsto_lim hbdd

/-- **A-priori exponential bound.** `τ(0, n v) ≤ exp(-n · inf_m -log τ(0, m v) / m)` for every
`n`. -/
theorem tau_le_exp_neg_mul (q : Sym2 G → unitInterval) (v : G)
    (hpos : ∀ n : ℕ, 0 < tau q 0 (n • v)) (n : ℕ) :
    (tau q 0 (n • v)).toReal ≤
      Real.exp (-(n : ℝ) * ⨅ m : ℕ+, -Real.log (tau q 0 ((m : ℕ) • v)).toReal / m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [zero_nsmul, tau_self, ENNReal.toReal_one, Nat.cast_zero, neg_zero, zero_mul,
      Real.exp_zero, le_refl]
  · have hb : BddBelow (range fun n : ℕ+ => -Real.log (tau q 0 ((n : ℕ) • v)).toReal / n) :=
      ⟨0, by
        rintro _ ⟨n, rfl⟩
        exact div_nonneg (neg_log_tau_nonneg q _ _) (Nat.cast_nonneg _)⟩
    have hle := ciInf_le hb ⟨n, hn⟩
    simp only [PNat.mk_coe] at hle
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hmul : (n : ℝ) * (⨅ m : ℕ+, -Real.log (tau q 0 ((m : ℕ) • v)).toReal / m) ≤
        -Real.log (tau q 0 (n • v)).toReal := by
      rw [le_div_iff₀ hnpos] at hle
      linarith
    have hτ := tau_toReal_pos (hpos n)
    calc (tau q 0 (n • v)).toReal = Real.exp (-(-Real.log (tau q 0 (n • v)).toReal)) := by
          rw [neg_neg, Real.exp_log hτ]
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)

end Fekete

/-! ### Non-vacuity -/

/-- With every pair open with probability one, `τ ≡ 1` on `ℤ`, so both hypotheses of
`tendsto_neg_log_tau_div` hold. -/
theorem tau_one_eq_one {V : Type*} (x y : V) : tau (fun _ : Sym2 V => (1 : unitInterval)) x y = 1 := by
  rcases eq_or_ne x y with rfl | hxy
  · exact tau_self _ x
  · refine le_antisymm (tau_le_one _ _ _) ?_
    have h := prodBernoulli_setOf_mem (fun _ : Sym2 V => (1 : unitInterval)) s(x, y)
    simp only [unitInterval.toNNReal, Set.Icc.coe_one] at h
    calc (1 : ℝ≥0∞) = prodBernoulli (fun _ : Sym2 V => (1 : unitInterval)) {ω | s(x, y) ∈ ω} := by
          rw [h]; rfl
      _ ≤ tau _ x y := measure_mono fun ω hω => mem_conn_of_mem hxy hω

example (v : ℤ) : Tendsto (fun n : ℕ =>
    -Real.log (tau (fun _ : Sym2 ℤ => (1 : unitInterval)) 0 (n • v)).toReal / n) atTop
      (nhds (⨅ n : ℕ+, -Real.log (tau (fun _ : Sym2 ℤ => (1 : unitInterval)) 0
        ((n : ℕ) • v)).toReal / n)) :=
  tendsto_neg_log_tau_div _ v (fun x y g => by rw [tau_one_eq_one, tau_one_eq_one])
    (fun n => by rw [tau_one_eq_one]; exact one_pos)

end PercLib.Percolation.Bond

end
