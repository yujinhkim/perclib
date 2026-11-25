/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 123, Q-7). No upstream proof is copied.
-/
module

public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Pi.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Power-law kernels on `ℤ^d`

`ℤ^d` is `Fin d → ℤ` with mathlib's sup norm `‖z‖ = max_i |z_i|`. The power-law kernel with
exponent `d + α` is `z ↦ if z = 0 then 0 else ‖z‖ ^ (-(d + α))`; the `if` avoids
`0 ^ 0 = 1` in `Real.rpow`. It is written as a lambda: this file adds no definition.

* Shell counts: `#{‖z‖ ≤ n} = (2n+1)^d`, `#{‖z‖ = n} = (2n+1)^d - (2n-1)^d` for `n ≥ 1`, and
  `2d(2n-1)^(d-1) ≤ #{‖z‖ = n} ≤ 2d(2n+1)^(d-1)`.
* Summability: for `d ≥ 1` the kernel is summable exactly when `0 < α`, and its `ℝ≥0∞`-sum
  is `⊤` when `α ≤ 0`.
* Tail bound: for `α > 0`, `∑_{‖z‖ ≥ r} ‖z‖^(-(d+α)) ≤ C r^(-α)` for real `r ≥ 1`.
* The kernel is even.

When `d = 0` the only point is `0`, every sum is `0`, and the summability statement fails
for `α ≤ 0`; so `1 ≤ d` is a hypothesis there.

Method: every norm is a natural number, so a sum over `ℤ^d` is a sum over shells, each shell
has between `n^(d-1)` and `2d·3^(d-1)·n^(d-1)` points, and the problem reduces to the
`p`-series `∑ n^(-(1+α))`. Its tail is bounded by telescoping.
-/

@[expose] public section

noncomputable section

open Finset
open scoped ENNReal

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-! ### Norms are natural numbers -/

theorem natCast_natAbs_eq_norm (k : ℤ) : ((k.natAbs : ℕ) : ℝ) = ‖k‖ := by
  rw [Int.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]

/-- The sup norm is at most `n` exactly when every coordinate has absolute value at most
`n`. -/
theorem norm_le_natCast_iff (z : Fin d → ℤ) (n : ℕ) :
    ‖z‖ ≤ n ↔ ∀ i, (z i).natAbs ≤ n := by
  rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg n)]
  refine forall_congr' fun i => ?_
  rw [← natCast_natAbs_eq_norm, Nat.cast_le]

/-- The sup norm of an integer point is a natural number. -/
theorem natCast_floor_norm (z : Fin d → ℤ) : ((⌊‖z‖⌋₊ : ℕ) : ℝ) = ‖z‖ := by
  refine le_antisymm (Nat.floor_le (norm_nonneg _)) ?_
  rw [norm_le_natCast_iff]
  intro i
  rw [Nat.le_floor_iff (norm_nonneg _), natCast_natAbs_eq_norm]
  exact norm_le_pi_norm z i

theorem floor_norm_eq_iff (z : Fin d → ℤ) (n : ℕ) : ⌊‖z‖⌋₊ = n ↔ ‖z‖ = n := by
  constructor
  · intro h
    rw [← natCast_floor_norm z, h]
  · intro h
    rw [h, Nat.floor_natCast]

theorem floor_norm_eq_zero_iff (z : Fin d → ℤ) : ⌊‖z‖⌋₊ = 0 ↔ z = 0 := by
  rw [floor_norm_eq_iff, Nat.cast_zero, norm_eq_zero]

/-! ### Balls and shells -/

theorem mem_Icc_iff_norm_le (z : Fin d → ℤ) (n : ℕ) :
    z ∈ Finset.Icc (fun _ => -(n : ℤ)) (fun _ => (n : ℤ)) ↔ ‖z‖ ≤ n := by
  rw [Finset.mem_Icc, norm_le_natCast_iff, Pi.le_def, Pi.le_def, ← forall_and]
  refine forall_congr' fun i => ?_
  omega

theorem card_Icc_ball (n : ℕ) :
    #(Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))) = (2 * n + 1) ^ d := by
  rw [Pi.card_Icc]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- The ball of radius `n` in `ℤ^d` has `(2n+1)^d` points. -/
theorem card_norm_le (d n : ℕ) :
    Nat.card {z : Fin d → ℤ // ‖z‖ ≤ n} = (2 * n + 1) ^ d := by
  rw [← card_Icc_ball n, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun z => (mem_Icc_iff_norm_le z n).symm)

theorem finite_norm_le (n : ℕ) : {z : Fin d → ℤ | ‖z‖ ≤ n}.Finite :=
  (Finset.Icc (fun _ : Fin d => -(n : ℤ)) (fun _ => (n : ℤ))).finite_toSet.subset
    fun z hz => (mem_Icc_iff_norm_le z n).2 hz

theorem finite_floor_norm_eq (n : ℕ) : Finite {z : Fin d → ℤ // ⌊‖z‖⌋₊ = n} :=
  ((finite_norm_le n).subset fun z (hz : ⌊‖z‖⌋₊ = n) =>
    le_of_eq ((floor_norm_eq_iff z n).1 hz)).to_subtype

/-- The sphere of radius `n ≥ 1` in `ℤ^d` has `(2n+1)^d - (2n-1)^d` points. -/
theorem card_norm_eq (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {z : Fin d → ℤ // ‖z‖ = n} = (2 * n + 1) ^ d - (2 * n - 1) ^ d := by
  have h2 : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [h2, ← card_Icc_ball (d := d) n, ← card_Icc_ball (d := d) (n - 1),
    ← Finset.card_sdiff_of_subset, ← Nat.card_eq_finsetCard]
  · refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    rw [Finset.mem_sdiff, mem_Icc_iff_norm_le, mem_Icc_iff_norm_le, ← natCast_floor_norm z,
      Nat.cast_le, Nat.cast_le, Nat.cast_inj]
    omega
  · intro z hz
    rw [mem_Icc_iff_norm_le] at hz ⊢
    exact hz.trans (Nat.cast_le.2 (Nat.sub_le n 1))

theorem pow_add_two_le (b e : ℕ) : (b + 2) ^ (e + 1) ≤ b ^ (e + 1) + 2 * (e + 1) * (b + 2) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hb : b ^ (e + 1) ≤ (b + 2) ^ (e + 1) := Nat.pow_le_pow_left (by omega) _
    calc (b + 2) ^ (e + 1 + 1) = (b + 2) * (b + 2) ^ (e + 1) := by ring
      _ ≤ (b + 2) * (b ^ (e + 1) + 2 * (e + 1) * (b + 2) ^ e) := Nat.mul_le_mul_left _ ih
      _ = b ^ (e + 1 + 1) + 2 * b ^ (e + 1) + 2 * (e + 1) * (b + 2) ^ (e + 1) := by ring
      _ ≤ b ^ (e + 1 + 1) + 2 * (b + 2) ^ (e + 1) + 2 * (e + 1) * (b + 2) ^ (e + 1) := by
        gcongr
      _ = b ^ (e + 1 + 1) + 2 * (e + 1 + 1) * (b + 2) ^ (e + 1) := by ring

theorem le_pow_add_two (b e : ℕ) : b ^ (e + 1) + 2 * (e + 1) * b ^ e ≤ (b + 2) ^ (e + 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    calc b ^ (e + 1 + 1) + 2 * (e + 1 + 1) * b ^ (e + 1)
        ≤ (b + 2) * (b ^ (e + 1) + 2 * (e + 1) * b ^ e) := by
          have : (b + 2) * (b ^ (e + 1) + 2 * (e + 1) * b ^ e) = b ^ (e + 1 + 1) +
              2 * (e + 1 + 1) * b ^ (e + 1) + 4 * (e + 1) * b ^ e := by ring
          rw [this]
          exact Nat.le_add_right _ _
      _ ≤ (b + 2) * (b + 2) ^ (e + 1) := Nat.mul_le_mul_left _ ih
      _ = (b + 2) ^ (e + 1 + 1) := by ring

/-- Bounds on the sphere: `2d(2n-1)^(d-1) ≤ #{‖z‖ = n} ≤ 2d(2n+1)^(d-1)` for `n, d ≥ 1`. -/
theorem card_norm_eq_bounds {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    2 * d * (2 * n - 1) ^ (d - 1) ≤ Nat.card {z : Fin d → ℤ // ‖z‖ = n} ∧
      Nat.card {z : Fin d → ℤ // ‖z‖ = n} ≤ 2 * d * (2 * n + 1) ^ (d - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, 2 * n - 1 = b := ⟨_, rfl⟩
  have hb2 : 2 * n + 1 = b + 2 := by omega
  rw [card_norm_eq _ hn, hb, hb2, Nat.add_sub_cancel]
  have h1 := pow_add_two_le b e
  have h2 := le_pow_add_two b e
  constructor <;> omega

/-! ### Sums over `ℤ^d` as sums over shells -/

/-- A sum of a function of the norm is a sum over shells. -/
theorem tsum_comp_floor_norm (g : ℕ → ℝ≥0∞) :
    ∑' z : Fin d → ℤ, g ⌊‖z‖⌋₊ =
      ∑' n : ℕ, (Nat.card {z : Fin d → ℤ // ‖z‖ = n} : ℝ≥0∞) * g n := by
  rw [← (Equiv.sigmaFiberEquiv fun z : Fin d → ℤ => ⌊‖z‖⌋₊).tsum_eq, ENNReal.tsum_sigma']
  congr 1
  funext n
  have := finite_floor_norm_eq (d := d) n
  have h : ∀ x : {z : Fin d → ℤ // ⌊‖z‖⌋₊ = n},
      g ⌊‖(Equiv.sigmaFiberEquiv fun z : Fin d → ℤ => ⌊‖z‖⌋₊) ⟨n, x⟩‖⌋₊ = g n :=
    fun x => congrArg g x.2
  rw [tsum_congr h, ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe,
    Nat.card_congr (Equiv.subtypeEquivRight fun z => floor_norm_eq_iff z n)]

/-- For `d ≥ 1`, each shell `n ≥ 1` has between `n^(d-1)` and `2d·3^(d-1)·n^(d-1)` points. -/
theorem card_norm_eq_le_le {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    n ^ (d - 1) ≤ Nat.card {z : Fin d → ℤ // ‖z‖ = n} ∧
      Nat.card {z : Fin d → ℤ // ‖z‖ = n} ≤ 2 * d * 3 ^ (d - 1) * n ^ (d - 1) := by
  obtain ⟨h1, h2⟩ := card_norm_eq_bounds hd hn
  constructor
  · calc n ^ (d - 1) ≤ (2 * n - 1) ^ (d - 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ 2 * d * (2 * n - 1) ^ (d - 1) := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ _ := h1
  · calc _ ≤ 2 * d * (2 * n + 1) ^ (d - 1) := h2
      _ ≤ 2 * d * (3 * n) ^ (d - 1) := by gcongr; omega
      _ = 2 * d * 3 ^ (d - 1) * n ^ (d - 1) := by ring

/-- Two-sided comparison of a radial sum over `ℤ^d` with a sum over `ℕ`. -/
theorem tsum_comp_floor_norm_bounds (hd : 1 ≤ d) (g : ℕ → ℝ≥0∞) (hg : g 0 = 0) :
    ∑' n : ℕ, ((n ^ (d - 1) : ℕ) : ℝ≥0∞) * g n ≤ ∑' z : Fin d → ℤ, g ⌊‖z‖⌋₊ ∧
      ∑' z : Fin d → ℤ, g ⌊‖z‖⌋₊ ≤
        ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ≥0∞) * ∑' n : ℕ, ((n ^ (d - 1) : ℕ) : ℝ≥0∞) * g n := by
  rw [tsum_comp_floor_norm, ← ENNReal.tsum_mul_left]
  constructor
  · refine ENNReal.tsum_le_tsum fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hg]
    · gcongr
      exact (card_norm_eq_le_le hd hn).1
  · refine ENNReal.tsum_le_tsum fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hg]
    · rw [← mul_assoc, ← Nat.cast_mul]
      gcongr
      exact (card_norm_eq_le_le hd hn).2

/-! ### The `p`-series -/

theorem summable_iff_tsum_ofReal_ne_top {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    Summable f ↔ ∑' i, ENNReal.ofReal (f i) ≠ ∞ := by
  refine ⟨Summable.tsum_ofReal_ne_top, fun h => ?_⟩
  have := ENNReal.summable_toNNReal_of_tsum_ne_top h
  refine (NNReal.summable_coe.2 this).congr fun i => ?_
  rw [Function.comp_apply, ENNReal.ofReal, ENNReal.toNNReal_coe, Real.coe_toNNReal _ (hf i)]

theorem summable_ite_rpow_iff (p : ℝ) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ p) ↔ p < -1 := by
  rw [← Real.summable_nat_rpow, ← summable_nat_add_iff 1,
    ← summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ p) 1]
  simp

/-- For `n ≥ 1`, `n^(d-1) · n^(-(d+α)) = n^(-(1+α))`. -/
theorem pow_mul_rpow_neg (hd : 1 ≤ d) (α : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ((n ^ (d - 1) : ℕ) : ℝ) * (n : ℝ) ^ (-((d : ℝ) + α)) = (n : ℝ) ^ (-(1 + α)) := by
  have hpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_add hpos, Nat.cast_sub hd]
  congr 1
  push_cast
  ring

/-- The key one-step inequality: `α (x+1)^(-(1+α)) ≤ x^(-α) - (x+1)^(-α)` for `x > 0`. -/
theorem mul_rpow_le_sub (α : ℝ) (hα : 0 < α) {x : ℝ} (hx : 0 < x) :
    α * (x + 1) ^ (-(1 + α)) ≤ x ^ (-α) - (x + 1) ^ (-α) := by
  set y := x + 1 with hy
  have hy0 : 0 < y := by positivity
  have hlog : 1 / y ≤ Real.log (y / x) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hx hy0)
    have hl : Real.log (y / x) = -Real.log (x / y) := by rw [← Real.log_inv, inv_div]
    have : x / y - 1 = -(1 / y) := by field_simp; ring
    linarith
  have hexp : 1 + α / y ≤ (y / x) ^ α := by
    rw [Real.rpow_def_of_pos (div_pos hy0 hx)]
    have := Real.add_one_le_exp (Real.log (y / x) * α)
    have : α * (1 / y) ≤ α * Real.log (y / x) := mul_le_mul_of_nonneg_left hlog hα.le
    rw [mul_one_div] at this
    linarith
  have hx' : x ^ (-α) = y ^ (-α) * (y / x) ^ α := by
    rw [Real.div_rpow hy0.le hx.le, Real.rpow_neg hy0.le, Real.rpow_neg hx.le]
    have : 0 < y ^ α := Real.rpow_pos_of_pos hy0 α
    field_simp
  have hy' : y ^ (-(1 + α)) = y ^ (-α) / y := by
    rw [show -(1 + α) = -α + -1 by ring, Real.rpow_add hy0, Real.rpow_neg_one, div_eq_mul_inv]
  rw [hx', hy']
  have : 0 < y ^ (-α) := Real.rpow_pos_of_pos hy0 _
  have : α * (y ^ (-α) / y) = y ^ (-α) * (α / y) := by ring
  nlinarith

/-- Tail of the `p`-series with `p = 1 + α > 1`, by telescoping. -/
theorem sum_range_ite_rpow_le (α : ℝ) (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    ∑ n ∈ range N, (if m ≤ n then (n : ℝ) ^ (-(1 + α)) else 0) ≤
      ((m : ℝ) ^ (-α) / α + (m : ℝ) ^ (-(1 + α))) -
        (if m ≤ N then (N : ℝ) ^ (-α) / α + (N : ℝ) ^ (-(1 + α))
          else (m : ℝ) ^ (-α) / α + (m : ℝ) ^ (-(1 + α))) := by
  induction N with
  | zero => simp [show ¬ m ≤ 0 by omega]
  | succ N ih =>
    rw [sum_range_succ]
    by_cases hmN : m ≤ N
    · rw [ite_eq_left hmN] at ih
      rw [ite_eq_left hmN, ite_eq_left (by omega)]
      have hN : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
      have key := mul_rpow_le_sub α hα hN
      have key2 : (N : ℝ) ^ (-(1 + α)) - ((N : ℝ) + 1) ^ (-(1 + α)) ≥ 0 := by
        have : (N : ℝ) ^ (-(1 + α)) ≥ ((N : ℝ) + 1) ^ (-(1 + α)) :=
          Real.rpow_le_rpow_of_nonpos hN (by linarith) (by linarith)
        linarith
      push_cast
      have : ((N : ℝ) + 1) ^ (-(1 + α)) ≤ ((N : ℝ) ^ (-α) - ((N : ℝ) + 1) ^ (-α)) / α := by
        rw [le_div_iff₀ hα]; linarith
      have hdiv : ((N : ℝ) ^ (-α) - ((N : ℝ) + 1) ^ (-α)) / α =
          (N : ℝ) ^ (-α) / α - ((N : ℝ) + 1) ^ (-α) / α := sub_div _ _ _
      linarith
    · rw [ite_eq_right hmN] at ih
      rw [ite_eq_right hmN, add_zero]
      by_cases hmN1 : m ≤ N + 1
      · have hm' : m = N + 1 := by omega
        rw [ite_eq_left hmN1, ← hm']
        simpa using ih
      · rw [ite_eq_right hmN1]
        exact ih

/-- Tail bound for the `p`-series: `∑_{n ≥ r} n^(-(1+α)) ≤ (1 + 1/α) r^(-α)` for `r ≥ 1`. -/
theorem tsum_ite_rpow_le (α : ℝ) (hα : 0 < α) {r : ℝ} (hr : 1 ≤ r) :
    ∑' n : ℕ, ENNReal.ofReal (if r ≤ n then (n : ℝ) ^ (-(1 + α)) else 0) ≤
      ENNReal.ofReal ((1 + 1 / α) * r ^ (-α)) := by
  set m := ⌈r⌉₊ with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by
    rw [hm, Ne, Nat.ceil_eq_zero, not_le]; linarith)
  have hiff : ∀ n : ℕ, r ≤ n ↔ m ≤ n := fun n => (Nat.ceil_le).symm
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 hm1
  have hmr : (m : ℝ) ^ (-α) ≤ r ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (Nat.le_ceil r) (by linarith)
  have hbound : (m : ℝ) ^ (-α) / α + (m : ℝ) ^ (-(1 + α)) ≤ (1 + 1 / α) * r ^ (-α) := by
    have h1 : (m : ℝ) ^ (-(1 + α)) ≤ (m : ℝ) ^ (-α) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm1) (by linarith)
    have h2 : 0 ≤ (m : ℝ) ^ (-α) := Real.rpow_nonneg hmpos.le _
    have h3 : (m : ℝ) ^ (-α) / α ≤ r ^ (-α) / α := div_le_div_of_nonneg_right hmr hα.le
    rw [add_mul, one_mul, mul_comm, ← div_eq_mul_one_div]
    linarith
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => by
    split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact le_rfl]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [hiff]
  refine (sum_range_ite_rpow_le α hα hm1 N).trans (le_trans ?_ hbound)
  have hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ x ^ (-α) / α + x ^ (-(1 + α)) := fun x hx =>
    add_nonneg (div_nonneg (Real.rpow_nonneg hx _) hα.le) (Real.rpow_nonneg hx _)
  split_ifs
  · linarith [hpos N (Nat.cast_nonneg N)]
  · linarith [hpos m (Nat.cast_nonneg m)]

/-! ### The power-law kernel -/

/-- The power-law kernel is a function of the (natural) norm. -/
theorem powerLaw_eq_comp_floor_norm (s : ℝ) (z : Fin d → ℤ) :
    (if z = 0 then (0 : ℝ) else ‖z‖ ^ (-s)) =
      (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-s)) ⌊‖z‖⌋₊ := by
  simp only [floor_norm_eq_zero_iff, natCast_floor_norm]

theorem powerLaw_nonneg (s : ℝ) (z : Fin d → ℤ) :
    0 ≤ (if z = 0 then (0 : ℝ) else ‖z‖ ^ (-s)) := by
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (norm_nonneg _) _

/-- The `ℝ≥0∞`-sum of the power-law kernel is comparable to the `p`-series with
`p = 1 + α`. -/
theorem tsum_ofReal_powerLaw_bounds (hd : 1 ≤ d) (α : ℝ) :
    ∑' n : ℕ, ENNReal.ofReal (if n = 0 then 0 else (n : ℝ) ^ (-(1 + α))) ≤
        ∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))) ∧
      ∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))) ≤
        ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ≥0∞) *
          ∑' n : ℕ, ENNReal.ofReal (if n = 0 then 0 else (n : ℝ) ^ (-(1 + α))) := by
  have hg : ∀ n : ℕ, ((n ^ (d - 1) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (if n = 0 then 0 else (n : ℝ) ^ (-((d : ℝ) + α))) =
        ENNReal.ofReal (if n = 0 then 0 else (n : ℝ) ^ (-(1 + α))) := by
    intro n
    split_ifs with hn
    · simp
    · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        pow_mul_rpow_neg hd α hn]
  simp_rw [powerLaw_eq_comp_floor_norm, ← hg]
  exact tsum_comp_floor_norm_bounds hd
    (fun n => ENNReal.ofReal (if n = 0 then 0 else (n : ℝ) ^ (-((d : ℝ) + α)))) (by simp)

/-- The `ℝ≥0∞`-sum of the power-law kernel is finite exactly when `0 < α` (for `d ≥ 1`). -/
theorem tsum_ofReal_powerLaw_ne_top_iff (hd : 1 ≤ d) (α : ℝ) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))) ≠ ∞ ↔
      0 < α := by
  obtain ⟨h1, h2⟩ := tsum_ofReal_powerLaw_bounds hd α
  have hser : ∑' n : ℕ, ENNReal.ofReal (if n = 0 then 0 else (n : ℝ) ^ (-(1 + α))) ≠ ∞ ↔
      0 < α := by
    rw [← summable_iff_tsum_ofReal_ne_top, summable_ite_rpow_iff]
    · constructor <;> intro h <;> linarith
    · intro n
      split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  constructor
  · intro h
    exact hser.1 (ne_top_of_le_ne_top h h1)
  · intro h
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hser.2 h)) h2

/-- The `ℝ≥0∞`-sum of the power-law kernel is finite exactly when `0 < α`. -/
theorem tsum_ofReal_powerLaw_lt_top_iff (hd : 1 ≤ d) (α : ℝ) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))) < ∞ ↔
      0 < α := by
  rw [lt_top_iff_ne_top, tsum_ofReal_powerLaw_ne_top_iff hd]

/-- For `α ≤ 0` the `ℝ≥0∞`-sum of the power-law kernel is infinite. -/
theorem tsum_ofReal_powerLaw_eq_top (hd : 1 ≤ d) {α : ℝ} (hα : α ≤ 0) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))) = ∞ := by
  by_contra h
  exact absurd ((tsum_ofReal_powerLaw_ne_top_iff hd α).1 h) (not_lt.2 hα)

/-- The power-law kernel on `ℤ^d` is summable exactly when `0 < α` (for `d ≥ 1`). -/
theorem summable_powerLaw_iff {d : ℕ} (hd : 1 ≤ d) (α : ℝ) :
    Summable (fun z : Fin d → ℤ => if z = 0 then (0 : ℝ) else ‖z‖ ^ (-((d : ℝ) + α))) ↔
      0 < α := by
  rw [summable_iff_tsum_ofReal_ne_top (powerLaw_nonneg _), tsum_ofReal_powerLaw_ne_top_iff hd]

/-- Tail bound in `ℝ≥0∞`. -/
theorem tsum_ofReal_powerLaw_tail_le (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {r : ℝ} (hr : 1 ≤ r) :
    ∑' z : Fin d → ℤ, ENNReal.ofReal (if r ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) ≤
      ENNReal.ofReal ((2 * d * 3 ^ (d - 1) : ℕ) * ((1 + 1 / α) * r ^ (-α))) := by
  have hcomp : ∀ z : Fin d → ℤ, (if r ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) =
      (fun n : ℕ => if r ≤ n then (n : ℝ) ^ (-((d : ℝ) + α)) else 0) ⌊‖z‖⌋₊ := by
    intro z
    simp only [natCast_floor_norm]
  have hg : ∀ n : ℕ, ((n ^ (d - 1) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (if r ≤ n then (n : ℝ) ^ (-((d : ℝ) + α)) else 0) =
        ENNReal.ofReal (if r ≤ n then (n : ℝ) ^ (-(1 + α)) else 0) := by
    intro n
    split_ifs with hn
    · have hn0 : n ≠ 0 := by
        rintro rfl
        simp at hn
        linarith
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        pow_mul_rpow_neg hd α hn0]
    · simp
  have h0 : ENNReal.ofReal (if r ≤ ((0 : ℕ) : ℝ) then ((0 : ℕ) : ℝ) ^ (-((d : ℝ) + α))
      else 0) = 0 := by
    rw [ite_eq_right (by simp; linarith), ENNReal.ofReal_zero]
  simp_rw [hcomp]
  refine ((tsum_comp_floor_norm_bounds hd (fun n : ℕ =>
    ENNReal.ofReal (if r ≤ (n : ℝ) then (n : ℝ) ^ (-((d : ℝ) + α)) else 0)) h0).2).trans ?_
  simp_rw [hg]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  gcongr
  exact tsum_ite_rpow_le α hα hr

/-- **Tail bound.** For `α > 0` and `d ≥ 1` there is `C` with
`∑_{‖z‖ ≥ r} ‖z‖^(-(d+α)) ≤ C r^(-α)` for every real `r ≥ 1`. One may take
`C = 2d·3^(d-1)·(1 + 1/α)`. -/
theorem tsum_powerLaw_tail_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      ∑' z : Fin d → ℤ, (if r ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) ≤ C * r ^ (-α) := by
  refine ⟨(2 * d * 3 ^ (d - 1) : ℕ) * (1 + 1 / α), fun r hr => ?_⟩
  have hnn : ∀ z : Fin d → ℤ, 0 ≤ (if r ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0) := by
    intro z
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hC : 0 ≤ ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (1 + 1 / α) * r ^ (-α) := by
    have : 0 ≤ r ^ (-α) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ 1 + 1 / α := by positivity
    positivity
  by_cases hs : Summable fun z : Fin d → ℤ =>
      (if r ≤ ‖z‖ then ‖z‖ ^ (-((d : ℝ) + α)) else 0)
  · rw [← ENNReal.ofReal_le_ofReal_iff hC, ENNReal.ofReal_tsum_of_nonneg hnn hs, mul_assoc]
    exact tsum_ofReal_powerLaw_tail_le hd hα hr
  · rw [tsum_eq_zero_of_not_summable hs]
    exact hC

/-- The power-law kernel is even. -/
theorem powerLaw_neg (s : ℝ) (z : Fin d → ℤ) :
    (if -z = 0 then (0 : ℝ) else ‖-z‖ ^ (-s)) = (if z = 0 then (0 : ℝ) else ‖z‖ ^ (-s)) := by
  simp only [neg_eq_zero, norm_neg]

/-! ### Non-vacuity -/

/-- The smallest case `d = 1, α = 1`: the kernel `1/z^2` on `ℤ` is summable. -/
example : Summable (fun z : Fin 1 → ℤ =>
    if z = 0 then (0 : ℝ) else ‖z‖ ^ (-(((1 : ℕ) : ℝ) + 1))) :=
  (summable_powerLaw_iff le_rfl 1).2 one_pos

/-- At the boundary `α = 0` the kernel is not summable, in every dimension `d ≥ 1`. -/
example (d : ℕ) (hd : 1 ≤ d) : ¬ Summable (fun z : Fin d → ℤ =>
    if z = 0 then (0 : ℝ) else ‖z‖ ^ (-((d : ℝ) + 0))) := by
  rw [summable_powerLaw_iff hd]
  exact lt_irrefl 0

/-- In dimension `0` the iff fails: the only point is `0`, so every kernel is summable. -/
example : Summable (fun z : Fin 0 → ℤ =>
    if z = 0 then (0 : ℝ) else ‖z‖ ^ (-(((0 : ℕ) : ℝ) + -1))) :=
  (hasSum_fintype _).summable

/-- The shell counts in `ℤ^2` at radius `1`: `9` points in the ball and `8` on the sphere. -/
example : Nat.card {z : Fin 2 → ℤ // ‖z‖ ≤ (1 : ℕ)} = 9 := card_norm_le 2 1
example : Nat.card {z : Fin 2 → ℤ // ‖z‖ = (1 : ℕ)} = 8 := card_norm_eq 2 le_rfl

end PercLib.Models.LongRange

end
