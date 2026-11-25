/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 214, Q-43, items 1 and 2). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.RowSum

/-!
# Two-point bounds from a convolution condition

Let `a` be a kernel with zero diagonal, row sums at most `m < 1` and `a * a ≤ K a` off the
diagonal with `K < 1`. The total weight `a^{*n}(x, y)` of `n`-step walks from `x` to `y`
satisfies `a^{*(n+1)}(x, y) ≤ c_{n+1} a(x, y)` for `x ≠ y`, where
`c_{n+1} = ∑_{k ≤ n} K^k m^{n-k}` (so `c_1 = 1`, `c_{n+2} = K c_{n+1} + m^{n+1}`), and
`∑ c_{n+1} = (1 - K)⁻¹ (1 - m)⁻¹`. Hence, when `a` dominates `q` off the diagonal,
`τ(x, y) ≤ a(x, y) (1 - K)⁻¹ (1 - m)⁻¹` for `x ≠ y`: the two-point function decays like
the kernel.

The walk weight from `x` to `y` is written inline as a sum over vertex sequences with an
endpoint indicator; no new definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The deterministic recursion -/

/-- The coefficients `c_{n+1} = ∑_{k ≤ n} K^k m^{n-k}` satisfy
`c_{n+2} = m^{n+1} + K c_{n+1}`. -/
theorem sum_range_pow_mul_pow_succ (K m : ℝ≥0∞) (n : ℕ) :
    ∑ k ∈ range (n + 2), K ^ k * m ^ (n + 1 - k) =
      m ^ (n + 1) + K * ∑ k ∈ range (n + 1), K ^ k * m ^ (n - k) := by
  rw [sum_range_succ', mul_sum, add_comm]
  congr 1
  · simp
  · refine sum_congr rfl fun k hk => ?_
    have hk' : k < n + 1 := mem_range.1 hk
    rw [show n + 1 - (k + 1) = n - k by omega, pow_succ]
    ring

/-- The coefficients sum to `(1 - K)⁻¹ (1 - m)⁻¹`. -/
theorem tsum_sum_range_pow_mul_pow (K m : ℝ≥0∞) :
    ∑' n : ℕ, ∑ k ∈ range (n + 1), K ^ k * m ^ (n - k) = (1 - K)⁻¹ * (1 - m)⁻¹ := by
  have hA : ∀ n : ℕ, ∑ k ∈ range (n + 1), K ^ k * m ^ (n - k) =
      ∑' k : ℕ, if k ≤ n then K ^ k * m ^ (n - k) else 0 := by
    intro n
    rw [tsum_eq_sum (s := range (n + 1)) fun k hk => ite_eq_right (by
      rw [Finset.mem_range] at hk; omega)]
    exact sum_congr rfl fun k hk => (ite_eq_left (by rw [Finset.mem_range] at hk; omega)).symm
  have hC : ∀ k : ℕ, (∑' n : ℕ, if k ≤ n then K ^ k * m ^ (n - k) else 0) =
      K ^ k * ∑' j : ℕ, m ^ j := by
    intro k
    rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := k)]
    rw [sum_eq_zero fun i hi => ite_eq_right (by rw [Finset.mem_range] at hi; omega), zero_add,
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [ite_eq_left (by omega), Nat.add_sub_cancel]
  simp_rw [hA]
  rw [ENNReal.tsum_comm]
  simp_rw [hC]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.tsum_geometric]

/-- **Walk sums (deterministic).** For any family `F n x y` obeying the first-step recursion of
`n`-step walk weights from `x` to `y`, with diagonal values at most `m^n`, the convolution
condition gives `F (n+1) x y ≤ c_{n+1} a x y` for `x ≠ y`. -/
theorem le_sum_range_mul_of_convolution (a : V → V → ℝ≥0∞) (m K : ℝ≥0∞)
    (hconv : ∀ x y, x ≠ y → ∑' z, a x z * a z y ≤ K * a x y)
    (F : ℕ → V → V → ℝ≥0∞) (hF0 : ∀ z y, F 0 z y = if z = y then 1 else 0)
    (hFs : ∀ n x y, F (n + 1) x y = ∑' z, a x z * F n z y)
    (hdiag : ∀ n y, F n y y ≤ m ^ n) :
    ∀ n x y, x ≠ y → F (n + 1) x y ≤ (∑ k ∈ range (n + 1), K ^ k * m ^ (n - k)) * a x y := by
  classical
  intro n
  induction n with
  | zero =>
    intro x y _
    rw [hFs]
    simp_rw [hF0, mul_ite, mul_one, mul_zero]
    rw [tsum_ite_eq]
    simp
  | succ n ih =>
    intro x y hxy
    rw [hFs, ENNReal.tsum_eq_add_tsum_ite y, sum_range_pow_mul_pow_succ, add_mul]
    refine add_le_add ?_ ?_
    · calc a x y * F (n + 1) y y ≤ a x y * m ^ (n + 1) := by gcongr; exact hdiag (n + 1) y
        _ = m ^ (n + 1) * a x y := mul_comm _ _
    · calc ∑' z, (if z = y then 0 else a x z * F (n + 1) z y)
          ≤ ∑' z, a x z * ((∑ k ∈ range (n + 1), K ^ k * m ^ (n - k)) * a z y) := by
            refine ENNReal.tsum_le_tsum fun z => ?_
            split_ifs with hz
            · exact bot_le
            · gcongr; exact ih z y hz
        _ = (∑ k ∈ range (n + 1), K ^ k * m ^ (n - k)) * ∑' z, a x z * a z y := by
            rw [← ENNReal.tsum_mul_left]
            congr 1
            funext z
            ring
        _ ≤ (∑ k ∈ range (n + 1), K ^ k * m ^ (n - k)) * (K * a x y) := by
            gcongr; exact hconv x y hxy
        _ = K * (∑ k ∈ range (n + 1), K ^ k * m ^ (n - k)) * a x y := by ring

/-! ### Walk weights with a prescribed endpoint -/

/-- First-step recursion for walk weights from `x` ending at `y`. -/
theorem tsum_walkWeight_end_succ (a : V → V → ℝ≥0∞) (n : ℕ) (x y : V) :
    (∑' p : Fin (n + 1) → V,
      if (List.ofFn p).getLastD x = y then walkWeight a x p else 0) =
      ∑' z, a x z * ∑' p : Fin n → V,
        if (List.ofFn p).getLastD z = y then walkWeight a z p else 0 := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => V)).tsum_eq]
  change (∑' p : V × (Fin n → V), if (List.ofFn (Fin.cons p.1 p.2 : Fin (n + 1) → V)).getLastD x = y then walkWeight a x (Fin.cons p.1 p.2) else 0) = _
  rw [ENNReal.tsum_prod']
  congr 1
  funext z
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext p
  rw [List.ofFn_succ, Fin.cons_zero, List.getLastD_cons, walkWeight_cons, mul_ite, mul_zero]
  simp only [Fin.cons_succ]

theorem tsum_walkWeight_end_zero (a : V → V → ℝ≥0∞) (z y : V) :
    (∑' p : Fin 0 → V,
      if (List.ofFn p).getLastD z = y then walkWeight a z p else 0) =
      if z = y then 1 else 0 := by
  rw [tsum_fintype, Fintype.sum_unique]
  simp

theorem tsum_walkWeight_end_le_walkSum (a : V → V → ℝ≥0∞) (n : ℕ) (x y : V) :
    (∑' p : Fin n → V,
      if (List.ofFn p).getLastD x = y then walkWeight a x p else 0) ≤
      walkSum a n x := by
  rw [walkSum_eq_tsum_walkWeight]
  refine ENNReal.tsum_le_tsum fun p => ?_
  split_ifs
  · exact le_rfl
  · exact bot_le

/-! ### Paths and walk weights -/

/-- Simple paths from `x` to `y` inject into vertex sequences ending at `y`, so the path sum is
at most the sum of walk weights with endpoint `y`. -/
theorem tsum_path_weight_le (b : V → V → ℝ≥0∞) (x y : V) :
    ∑' p : (⊤ : SimpleGraph V).Path x y, walkWeight b x p.1.support.tail.get ≤
      ∑' n, ∑' p : Fin n → V,
        if (List.ofFn p).getLastD x = y then walkWeight b x p else 0 := by
  classical
  have hinj : Function.Injective fun p : (⊤ : SimpleGraph V).Path x y => p.1.support.tail := by
    intro p r h
    have hs : p.1.support = r.1.support := by
      rw [← p.1.cons_tail_support, ← r.1.cons_tail_support]
      exact congrArg _ h
    exact Subtype.ext (SimpleGraph.Walk.support_injective hs)
  have hend : ∀ p : (⊤ : SimpleGraph V).Path x y,
      (List.ofFn p.1.support.tail.get).getLastD x = y := by
    intro p
    rw [List.ofFn_get]
    have h1 := p.1.getLast_support
    have h2 : p.1.support.getLast? = some y := by
      rw [List.getLast?_eq_some_getLast (h := p.1.support_ne_nil), h1]
    rw [← p.1.cons_tail_support, List.getLast?_cons] at h2
    rw [List.getLastD_eq_getLast?]
    simpa using h2
  set g : List V → ℝ≥0∞ := fun l =>
    if (List.ofFn l.get).getLastD x = y then walkWeight b x l.get else 0 with hg
  calc ∑' p : (⊤ : SimpleGraph V).Path x y, walkWeight b x p.1.support.tail.get
      = ∑' p : (⊤ : SimpleGraph V).Path x y, g p.1.support.tail := by
        congr 1
        funext p
        simp only [hg, hend p, ite_true]
    _ ≤ ∑' l : List V, g l := ENNReal.tsum_comp_le_tsum_of_injective hinj g
    _ = ∑' t : Σ n, Fin n → V, if (List.ofFn t.2).getLastD x = y
          then walkWeight b x t.2 else 0 :=
        (List.equivSigmaTuple.tsum_eq (fun t : Σ n, Fin n → V =>
          if (List.ofFn t.2).getLastD x = y
            then walkWeight b x t.2 else 0))
    _ = _ := ENNReal.tsum_sigma' _

/-! ### The two-point bound -/

/-- **Two-point bound from a convolution condition.** -/
theorem tau_le_of_convolution [Countable V] (q : Sym2 V → unitInterval) (a : V → V → ℝ≥0∞)
    (m K : ℝ≥0∞)
    (hqa : ∀ v w, v ≠ w → (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞) ≤ a v w)
    (hrow : ∀ v, ∑' w, offDiagonal a v w ≤ m)
    (hconv : ∀ x y, x ≠ y → ∑' z, offDiagonal a x z * offDiagonal a z y ≤ K * a x y)
    {x y : V} (hxy : x ≠ y) :
    tau q x y ≤ a x y * ((1 - K)⁻¹ * (1 - m)⁻¹) := by
  classical
  set b := offDiagonal a with hb
  set bq := offDiagonal (fun v w => (unitInterval.toNNReal (q s(v, w)) : ℝ≥0∞)) with hbq
  set F : ℕ → V → V → ℝ≥0∞ := fun n z y => ∑' p : Fin n → V,
    if (List.ofFn p).getLastD z = y then walkWeight b z p else 0 with hF
  have hbxy : ∀ u v, u ≠ v → b u v = a u v := fun u v huv => by
    simp [hb, offDiagonal_apply, huv.symm]
  have hle : ∀ u v, bq u v ≤ b u v := by
    intro u v
    simp only [hbq, hb, offDiagonal_apply]
    split_ifs with h
    · exact le_rfl
    · exact hqa u v (Ne.symm h)
  have hconv' : ∀ u v, u ≠ v → ∑' z, b u z * b z v ≤ K * b u v := fun u v huv => by
    rw [hbxy u v huv]; exact hconv u v huv
  have hbound := le_sum_range_mul_of_convolution b m K hconv' F
    (fun z y => tsum_walkWeight_end_zero b z y)
    (fun n x y => tsum_walkWeight_end_succ b n x y)
    (fun n y => (tsum_walkWeight_end_le_walkSum b n y y).trans
      (walkSum_masked_le_pow a m hrow n y))
  calc tau q x y
      ≤ ∑' p : (⊤ : SimpleGraph V).Path x y,
          ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) :=
        tau_le_tsum_paths q x y
    _ = ∑' p : (⊤ : SimpleGraph V).Path x y, walkWeight bq x p.1.support.tail.get := by
        simp_rw [path_prod_eq_weight]
        rfl
    _ ≤ ∑' p : (⊤ : SimpleGraph V).Path x y, walkWeight b x p.1.support.tail.get :=
        ENNReal.tsum_le_tsum fun p => Finset.prod_le_prod fun i _ => hle _ _
    _ ≤ ∑' n, F n x y := tsum_path_weight_le b x y
    _ = ∑' n, F (n + 1) x y := by
        rw [tsum_eq_zero_add' ENNReal.summable]
        have h0 : F 0 x y = 0 := by
          simp only [hF]
          rw [tsum_walkWeight_end_zero, ite_eq_right hxy]
        rw [h0, zero_add]
    _ ≤ ∑' n, (∑ k ∈ range (n + 1), K ^ k * m ^ (n - k)) * a x y := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [← hbxy x y hxy]
        exact hbound n x y hxy
    _ = a x y * ((1 - K)⁻¹ * (1 - m)⁻¹) := by
        rw [ENNReal.tsum_mul_right, tsum_sum_range_pow_mul_pow, mul_comm]

/-! ### Non-vacuity -/

/-- On two vertices, any profile at most `1/2` is dominated by the off-diagonal kernel `1/2`; the convolution condition holds with
`K = 0` (as for any kernel supported on a perfect matching) and the row sums are `1/2`. -/
example (q : Sym2 Bool → unitInterval) (hq : ∀ e, (unitInterval.toNNReal (q e) : ℝ≥0∞) ≤ 1 / 2) :
    tau q false true ≤ (fun _ _ : Bool => (1 / 2 : ℝ≥0∞)) false true * ((1 - 0)⁻¹ * (1 - 1 / 2)⁻¹) := by
  refine tau_le_of_convolution _ (fun _ _ : Bool => (1 / 2 : ℝ≥0∞)) (1 / 2) 0
    (fun v w _ => ?_) (fun v => ?_) (fun x y hxy => ?_) (by decide)
  · exact hq _
  · rw [tsum_fintype, Fintype.sum_bool]
    cases v <;> simp [offDiagonal_apply]
  · rw [tsum_fintype, Fintype.sum_bool]
    cases x <;> cases y <;> simp_all [offDiagonal_apply]

end PercLib.Percolation.Bond

end
