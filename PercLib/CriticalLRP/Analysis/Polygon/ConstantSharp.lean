/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Sharpness of the generic polygon constant on abstract finite kernels.
-/
module

public import PercLib.CriticalLRP.Analysis.Polygon.Core

open scoped BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.I418C

-- `Tconst` is declared in `Polygon/Defs.lean`.

@[simp] theorem Tconst_apply {N : ℕ} (x y : Fin N) : Tconst N x y = 1 := rfl

variable {N : ℕ} [NeZero N]

/-- Every matrix power of the constant-one kernel on `Fin N` is `N ^ (n - 1)` for `n ≥ 1`. -/
theorem polyK_Tconst (n : ℕ) (hn : 1 ≤ n) (x y : Fin N) :
    polyK (Tconst N) n x y = (N : ℝ) ^ (n - 1) := by
  induction n generalizing x y with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        rw [polyK_one]
        simp
      · rw [polyK_succ]
        have hterm : ∀ z : Fin N,
            polyK (Tconst N) n x z * Tconst N z y = (N : ℝ) ^ (n - 1) := by
          intro z
          rw [ih hpos x z, Tconst_apply, mul_one]
        rw [tsum_congr hterm, tsum_fintype, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [show n + 1 - 1 = (n - 1) + 1 from by omega, pow_succ]
        ring

/-- **Nontrivial witness of the abstract hypothesis bundle with `χ = N`.**

On `Fin N` with the constant-`1` kernel the whole `PowerInputs` bundle holds with
`nablaT = N²` (the value of every three-step entry) and `χ = N`; all `entry` and `colsum`
identities are *equalities*.  For `N ≥ 2` this has `χ = N > 1`, complementing the degenerate
`χ = 1` witness `T1` on `PUnit`. -/
theorem powerInputs_Tconst :
    PowerInputs (V := Fin N) (polyK (Tconst N)) ((N : ℝ) ^ 2) (N : ℝ) where
  nonneg n x y := polyK_nonneg _ (fun _ _ => zero_le_one) n x y
  base x y := polyK_zero _ x y
  comp n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [Nat.zero_add, polyK_zero, mul_ite, mul_one, mul_zero, tsum_ite_eq]
    · have hterm : ∀ y : Fin N,
          polyK (Tconst N) 3 0 y * polyK (Tconst N) n y 0
            = (N : ℝ) ^ 2 * (N : ℝ) ^ (n - 1) := by
        intro y
        rw [polyK_Tconst (N := N) 3 (by norm_num) 0 y,
          polyK_Tconst (N := N) n hpos y 0]
      rw [polyK_Tconst (N := N) (n + 3) (by omega) 0 0]
      rw [tsum_congr hterm, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [show n + 3 - 1 = 2 + (n - 1) + 1 from by omega, pow_add, pow_add, pow_one]
      ring
  compSummable n := Summable.of_finite
  colsum n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [polyK_zero, pow_zero, tsum_ite_eq]
    · have hterm : ∀ y : Fin N, polyK (Tconst N) n y 0 = (N : ℝ) ^ (n - 1) :=
        fun y => polyK_Tconst (N := N) n hpos y 0
      have hp : (N : ℝ) ^ n = (N : ℝ) ^ (n - 1) * (N : ℝ) := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ]
      rw [tsum_congr hterm, tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hp]
      ring
  colSummable n := Summable.of_finite
  entry n hn y := le_of_eq (polyK_Tconst (N := N) n hn y 0)
  selfOne := by
    rw [polyK_one]
    simp
  triSup y := by
    rw [polyK_Tconst (N := N) 3 (by norm_num) 0 y]

/-- **The estimate of `polygon_bound` is attained** in the constant-one instance on `Fin N`:
with `∇ = N²`, `χ = N`, `K = c₀ = N`, `r = R = 1`, `trc = 0`, `d = α = 1`, `cc = 1/4`, the two
sides are *equal* for every `ℓ ≥ 4`. -/
theorem polygon_bound_Tconst_eq (ell : ℕ) (hell : 4 ≤ ell) :
    polyK (Tconst N) ell 0 0
      = max 1 ((N : ℝ) ^ 2 * (N : ℝ) / (N : ℝ)) *
        ((0 : ℝ) + (1 : ℝ) ^ (-(1 / (4 * (1 : ℝ))))) * (N : ℝ) ^ (ell - 3) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hdiv : (N : ℝ) ^ 2 * (N : ℝ) / (N : ℝ) = (N : ℝ) ^ 2 := by
    field_simp
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hmax : max 1 ((N : ℝ) ^ 2 * (N : ℝ) / (N : ℝ)) = (N : ℝ) ^ 2 := by
    rw [hdiv, max_eq_right hNsq]
  have hone : (1 : ℝ) ^ (-(1 / (4 * (1 : ℝ)))) = 1 := Real.one_rpow _
  rw [hmax, hone, zero_add, mul_one, polyK_Tconst (N := N) ell (by omega) 0 0,
    show ell - 1 = 2 + (ell - 3) from by omega, pow_add]

/-- **The hypotheses of `polygon_bound` are jointly satisfiable in this instance.**

This is `polygon_bound` applied with the concrete data, so it witnesses that the conditional
estimate is *not* vacuous; together with `polygon_bound_Tconst_eq` it shows the constant is
attained. -/
theorem polygon_bound_Tconst (ell : ℕ) (hell : 4 ≤ ell) :
    polyK (Tconst N) ell 0 0
      ≤ max 1 ((N : ℝ) ^ 2 * (N : ℝ) / (N : ℝ)) *
        ((0 : ℝ) + (1 : ℝ) ^ (-(1 / (4 * (1 : ℝ))))) * (N : ℝ) ^ (ell - 3) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h := polygon_bound (P := polyK (Tconst N)) (nablaT := (N : ℝ) ^ 2) (χ := (N : ℝ))
    (powerInputs_Tconst (N := N)) (s := Finset.univ) (w := fun _ => (0 : ℝ))
    (r := 1) (R := 1) (trc := 0) (d := 1) (α := 1) (c₀ := (N : ℝ)) (K := (N : ℝ))
    (cc := 1 / (4 * (1 : ℝ))) (ell := ell)
    one_pos le_rfl hNpos (le_of_lt hNpos) le_rfl hell (by norm_num)
    (by intro y hy; simp at hy)
    (by
      intro y hy
      rw [Real.one_rpow] at hy
      linarith)
    le_rfl (by simp) (by rw [Real.one_rpow]) (by simp)
  simpa using h

/-- **The constant `max 1 (∇ K / c₀)` cannot be decreased.**

In the constant-one instance on `Fin N`, the assembled inequality is an equality, so any constant
`C` smaller than `max 1 (N² * N / N)` fails at `x = 0` for every `ℓ ≥ 4`. -/
theorem no_smaller_constant (ell : ℕ) (hell : 4 ≤ ell) {C : ℝ}
    (hC : C < max 1 ((N : ℝ) ^ 2 * (N : ℝ) / (N : ℝ))) :
    ¬ (polyK (Tconst N) ell 0 0
        ≤ C * ((0 : ℝ) + (1 : ℝ) ^ (-(1 / (4 * (1 : ℝ))))) * (N : ℝ) ^ (ell - 3)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hone : (1 : ℝ) ^ (-(1 / (4 * (1 : ℝ)))) = 1 := Real.one_rpow _
  have hpow : (0 : ℝ) < (N : ℝ) ^ (ell - 3) := pow_pos hNpos _
  intro h
  rw [polygon_bound_Tconst_eq (N := N) ell hell, hone, zero_add, mul_one, mul_one] at h
  have h2 : max 1 ((N : ℝ) ^ 2 * (N : ℝ) / (N : ℝ)) ≤ C :=
    le_of_mul_le_mul_right h hpow
  linarith

/-- **The additive `r^{-c}` term is indispensable**: the same instance has `trc = 0` and
`T^ℓ(0,0) = N ^ (ℓ-1) > 0`, so the RHS cannot be reduced to the `trc` summand alone. -/
theorem rpow_term_needed (ell : ℕ) (hell : 4 ≤ ell) :
    ¬ (polyK (Tconst N) ell 0 0
        ≤ max 1 ((N : ℝ) ^ 2 * (N : ℝ) / (N : ℝ)) * (0 : ℝ) * (N : ℝ) ^ (ell - 3)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  intro h
  rw [mul_zero, zero_mul, polyK_Tconst (N := N) ell (by omega) 0 0] at h
  have hpos : (0 : ℝ) < (N : ℝ) ^ (ell - 1) := pow_pos hNpos _
  linarith

end PercLib.CriticalLRP.I418C
