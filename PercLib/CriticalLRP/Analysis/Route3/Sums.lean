/- Integrated from independently rebuilt Ultramath work.
Production base 37c0efc68ae8ef365d8d155bc931fd784fdfde2b.
Scratch source: ../../.ultramath/smwvnrt0i/m2/Sums.lean.
-/

module

public import PercLib.CriticalLRP.Analysis.Route3.Defs

/-!
# Definitions and proofs: the head and tail sum bounds

Everything here is a statement about `ℕ`-indexed real sums.  Neither result mentions a
measure; they are consumed in `Main.lean` through `ENNReal.ofReal_sum_of_nonneg`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Analysis.Route3

/-! ### §1 The head bound `∑_{j<K} (j+1)^{-1/2} ≤ 2 √K` -/

theorem sum_range_inv_sqrt_le (K : ℕ) :
    ∑ j ∈ Finset.range K, (Real.sqrt ((j : ℝ) + 1))⁻¹ ≤ 2 * Real.sqrt (K : ℝ) := by
  induction K with
  | zero => simp
  | succ k ih =>
    have hstep : (Real.sqrt ((k : ℝ) + 1))⁻¹
        ≤ 2 * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ)) := by
      have hA : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      have hB : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      have hAB : 0 < Real.sqrt ((k : ℝ) + 1) + Real.sqrt (k : ℝ) := by linarith
      have hsq : (Real.sqrt ((k : ℝ) + 1)) ^ 2 - (Real.sqrt (k : ℝ)) ^ 2 = 1 := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        ring
      have hfac : (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ))
          * (Real.sqrt ((k : ℝ) + 1) + Real.sqrt (k : ℝ)) = 1 := by
        nlinarith
      have hdiff : Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ)
          = 1 / (Real.sqrt ((k : ℝ) + 1) + Real.sqrt (k : ℝ)) := by
        rw [eq_div_iff (ne_of_gt hAB)]
        linarith
      rw [hdiff]
      have h2 : (2 : ℝ) * (1 / (Real.sqrt ((k : ℝ) + 1) + Real.sqrt (k : ℝ)))
          = 2 / (Real.sqrt ((k : ℝ) + 1) + Real.sqrt (k : ℝ)) := by ring
      rw [h2, inv_eq_one_div, div_le_div_iff₀ hA hAB]
      have hle : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      nlinarith
    have hgoal : (∑ j ∈ Finset.range k, (Real.sqrt ((j : ℝ) + 1))⁻¹)
        + (Real.sqrt ((k : ℝ) + 1))⁻¹ ≤ 2 * Real.sqrt ((k : ℝ) + 1) := by
      nlinarith
    rw [Finset.sum_range_succ]
    simpa using hgoal

theorem sum_range_inv_sqrt_mono {K L : ℕ} (h : K ≤ L) :
    ∑ j ∈ Finset.range K, (Real.sqrt ((j : ℝ) + 1))⁻¹
      ≤ ∑ j ∈ Finset.range L, (Real.sqrt ((j : ℝ) + 1))⁻¹ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
    (fun i _ _ => by positivity)

/-! ### §2 The tail bound `∑_{N ≤ j < M} (j+1)^{-2} ≤ N^{-1}` -/

theorem sum_Ico_inv_sq_le (N M : ℕ) (hN : 1 ≤ N) :
    ∑ j ∈ Finset.Ico N M, (((j : ℝ) + 1) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ := by
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hstep : ∀ k ∈ Finset.range (M - N),
      ((((N + k : ℕ) : ℝ) + 1) ^ 2)⁻¹ ≤ ((N : ℝ) + k)⁻¹ - ((N : ℝ) + (k + 1))⁻¹ := by
    intro k _
    have h1 : (0 : ℝ) < (N : ℝ) + k := by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h2 : (0 : ℝ) < (N : ℝ) + (k + 1) := by linarith
    have hpos : (0 : ℝ) < ((N : ℝ) + k) * ((N : ℝ) + (k + 1)) := by positivity
    have hmono : ((N : ℝ) + k) * ((N : ℝ) + (k + 1)) ≤ ((N : ℝ) + k + 1) ^ 2 := by
      nlinarith
    have hle : 1 / (((N : ℝ) + k) + 1) ^ 2
        ≤ 1 / (((N : ℝ) + k) * ((N : ℝ) + (k + 1))) :=
      one_div_le_one_div_of_le hpos hmono
    have e1 : ((((N + k : ℕ) : ℝ) + 1) ^ 2)⁻¹ = 1 / (((N : ℝ) + k) + 1) ^ 2 := by
      push_cast
      ring
    have e2 : ((N : ℝ) + k)⁻¹ - ((N : ℝ) + (k + 1))⁻¹
        = 1 / (((N : ℝ) + k) * ((N : ℝ) + (k + 1))) := by
      field_simp
      ring
    rw [e1, e2]
    exact hle
  have htel : ∀ L : ℕ,
      ∑ k ∈ Finset.range L, (((N : ℝ) + k)⁻¹ - ((N : ℝ) + (k + 1))⁻¹)
        = (N : ℝ)⁻¹ - ((N : ℝ) + (L : ℝ))⁻¹ := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [Finset.sum_Ico_eq_sum_range]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [htel (M - N)]
  have hden : (0 : ℝ) ≤ (N : ℝ) + ((M - N : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((M - N : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have : (0 : ℝ) ≤ ((N : ℝ) + ((M - N : ℕ) : ℝ))⁻¹ := inv_nonneg.2 hden
  linarith

end PercLib.CriticalLRP.Analysis.Route3
