/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The weight layer: exactly how strong the subadditivity hypothesis is

Main results, none of which is in the repository yet.

1. `path_one_iff_subadd` : the `ℓ`-term estimate at `p = 1`, `A (∑_j u_j) ≤ ∑_j A (u_j)`, for
   *all* `ℓ`, is **equivalent** to subadditivity.  The `ℓ = 3` instance alone already gives it.
2. `subadd_iff_path_all` : consequently the whole family "`A (∑ u)^p ≤ ℓ^(max (p-1) 0) ∑ A u^p`
   for every `p ≥ 0` and every `ℓ`" is **equivalent** to subadditivity.  So adopting the full
   `ℓ`-term bound as a hypothesis is *not* a hidden strengthening of the source's assumption.
3. `path_ell_homog` : for `p ≥ 1` the `ℓ`-term estimate *implies* `ℓ`-homogeneity
   `A (ℓ • a) ≤ ℓ * A a`.
4. `A₄_hsub_not_homog` : `hsub` at `p = 4` holds for the repository's witness `A₄ : ZMod 4 → ℝ`,
   yet `ℓ`-homogeneity fails there.  So the gap between `hsub` and the `ℓ`-term estimate is
   visible already on a single repeated vector.
5. `A₄_hsub_not_subadd` : `hsub` at `p = 4` does not imply the two-term instance at `p = 1`
   either.  Hence `hsub` at `p > 1` is *incomparable* with subadditivity.
6. `path_rpow_le_sharp` : the constant `ℓ^(max (p-1) 0)` of `path_rpow_le` is attained for every
   `p ≥ 1` and every `ℓ ≥ 1`.  So the exponent `max (p - 1) 0` is forced.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.PathWeightedTreeSum

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset

variable {V : Type*} [AddCommGroup V]

/-! ## 1. The `ℓ`-term estimate at `p = 1` is exactly subadditivity -/

/-- **The `ℓ`-term estimate at `p = 1` is subadditivity, with no loss.** -/
theorem path_one_iff_subadd {A : V → ℝ} (hA0 : ∀ a : V, 0 ≤ A a) (h0 : A 0 = 0) :
    (∀ a b : V, A (a + b) ≤ A a + A b) ↔
      ∀ (ℓ : ℕ) (u : Fin ℓ → V), A (∑ j, u j) ≤ ∑ j, A (u j) := by
  constructor
  · intro hA ℓ u
    simpa using subadd_sum_le h0 hA (Finset.univ : Finset (Fin ℓ)) u
  · intro h a b
    have h3 := h 3 ![a, b, (0 : V)]
    simpa [Fin.sum_univ_three, h0] using h3

/-- **The full `ℓ`-term family is exactly subadditivity.** -/
theorem subadd_iff_path_all {A : V → ℝ} (hA0 : ∀ a : V, 0 ≤ A a) (h0 : A 0 = 0) :
    (∀ a b : V, A (a + b) ≤ A a + A b) ↔
      ∀ (p : ℝ), 0 ≤ p → ∀ (ℓ : ℕ), 1 ≤ ℓ → ∀ u : Fin ℓ → V,
        A (∑ j, u j) ^ p ≤ (ℓ : ℝ) ^ (max (p - 1) 0) * ∑ j, A (u j) ^ p := by
  constructor
  · intro hA p hp ℓ hℓ u
    exact path_rpow_le hA0 h0 hA hp hℓ u
  · intro h a b
    have h3 := h 1 zero_le_one 3 (by norm_num) ![a, b, (0 : V)]
    simpa [Fin.sum_univ_three, h0] using h3

/-! ## 2. What the `ℓ`-term estimate automatically buys: `ℓ`-homogeneity -/

/-- **The `ℓ`-term estimate forces `ℓ`-homogeneity on repeated vectors.** -/
theorem path_ell_homog {A : V → ℝ} (hA0 : ∀ a : V, 0 ≤ A a)
    {p : ℝ} (hp : 1 ≤ p)
    (hpath : ∀ (ℓ : ℕ), 1 ≤ ℓ → ∀ u : Fin ℓ → V,
      A (∑ j, u j) ^ p ≤ (ℓ : ℝ) ^ (max (p - 1) 0) * ∑ j, A (u j) ^ p)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : V) : A (ℓ • a) ≤ (ℓ : ℝ) * A a := by
  classical
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hppos : (0 : ℝ) < p := by linarith
  have h := hpath ℓ hℓ (fun _ : Fin ℓ => a)
  have hsum : (∑ j : Fin ℓ, (fun _ : Fin ℓ => a) j) = ℓ • a := by simp
  have hsum2 : (∑ j : Fin ℓ, A a ^ p) = (ℓ : ℝ) * A a ^ p := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum, hsum2, max_eq_left (by linarith : (0 : ℝ) ≤ p - 1)] at h
  have heq : (ℓ : ℝ) ^ (p - 1) * ((ℓ : ℝ) * A a ^ p) = ((ℓ : ℝ) * A a) ^ p := by
    rw [Real.mul_rpow hℓR.le (hA0 a)]
    have hp1 : (ℓ : ℝ) ^ p = (ℓ : ℝ) ^ (p - 1) * (ℓ : ℝ) := by
      nth_rewrite 1 [show p = (p - 1) + 1 by ring]
      rw [Real.rpow_add hℓR, Real.rpow_one]
    rw [hp1]
    ring
  rw [heq] at h
  by_contra hcon
  push Not at hcon
  exact absurd h (not_le.mpr (Real.rpow_lt_rpow (mul_nonneg hℓR.le (hA0 a)) hcon hppos))

/-! ## 3. The witness `A₄` of `PathWeightedTreeSum` against the sharpened question -/

/-- `A₄ 0 = 0`. -/
theorem A₄_zero : A₄ (0 : ZMod 4) = 0 := by
  unfold A₄
  simp

/-- `A₄ 1 = 1`. -/
theorem A₄_one : A₄ (1 : ZMod 4) = 1 := by
  have h0 : (1 : ZMod 4) ≠ 0 := by decide
  unfold A₄
  rw [ite_eq_right h0]
  simp

/-- `A₄ 2 = 2`. -/
theorem A₄_two : A₄ (2 : ZMod 4) = 2 := by
  have h0 : (2 : ZMod 4) ≠ 0 := by decide
  have h1 : (2 : ZMod 4) ≠ 1 := by decide
  unfold A₄
  rw [ite_eq_right h0, ite_eq_right h1]
  simp

/-- `A₄ 3 = 10/3`. -/
theorem A₄_three : A₄ (3 : ZMod 4) = 10 / 3 := by
  have h0 : (3 : ZMod 4) ≠ 0 := by decide
  have h1 : (3 : ZMod 4) ≠ 1 := by decide
  have h2 : (3 : ZMod 4) ≠ 2 := by decide
  unfold A₄
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]

/-- **`hsub` at `p = 4` does not imply the `p = 1` two-term inequality.** -/
theorem A₄_hsub_not_subadd : ¬ (∀ a b : ZMod 4, A₄ (a + b) ≤ A₄ a + A₄ b) := by
  intro h
  have h3 : A₄ ((1 : ZMod 4) + 2) ≤ A₄ 1 + A₄ 2 := h 1 2
  rw [show (1 : ZMod 4) + 2 = 3 from by decide, A₄_three, A₄_one, A₄_two] at h3
  norm_num at h3

/-- **`hsub` at `p = 4` does not imply `3`-homogeneity.** -/
theorem A₄_not_three_homog :
    ¬ (A₄ ((3 : ℕ) • (1 : ZMod 4)) ≤ (3 : ℝ) * A₄ 1) := by
  intro h
  have h3 : (3 : ℕ) • (1 : ZMod 4) = 3 := by decide
  rw [h3, A₄_three, A₄_one] at h
  norm_num at h

/-- **The sharp diagnosis of the gap.** -/
theorem A₄_hsub_not_homog :
    (∀ a b : ZMod 4,
        A₄ (a + b) ^ (4 : ℝ) ≤ (8 : ℝ) * (A₄ a ^ (4 : ℝ) + A₄ b ^ (4 : ℝ)))
      ∧ ¬ (A₄ ((3 : ℕ) • (1 : ZMod 4)) ≤ (3 : ℝ) * A₄ 1) :=
  ⟨A₄_hsub, A₄_not_three_homog⟩

/-! ## 4. The constant `ℓ^(max (p-1) 0)` cannot be improved -/

/-- **`path_rpow_le` is sharp.** -/
theorem path_rpow_le_sharp {p : ℝ} (hp : 1 ≤ p) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∃ (A : ℝ → ℝ) (u : Fin ℓ → ℝ),
      (∀ a, 0 ≤ A a) ∧ A 0 = 0 ∧ (∀ a b : ℝ, A (a + b) ≤ A a + A b) ∧
        A (∑ j, u j) ^ p = (ℓ : ℝ) ^ (max (p - 1) 0) * ∑ j, A (u j) ^ p := by
  classical
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  refine ⟨fun a => |a|, fun _ => 1, fun a => abs_nonneg a, by simp, ?_, ?_⟩
  · intro a b
    exact abs_add_le a b
  · have hL : (∑ j : Fin ℓ, (fun _ : Fin ℓ => (1 : ℝ)) j) = (ℓ : ℝ) := by simp
    have hR : (∑ j : Fin ℓ, |(1 : ℝ)| ^ p) = (ℓ : ℝ) := by simp
    show |(∑ j : Fin ℓ, (fun _ : Fin ℓ => (1 : ℝ)) j)| ^ p
      = (ℓ : ℝ) ^ (max (p - 1) 0) * (∑ j : Fin ℓ, |(1 : ℝ)| ^ p)
    rw [hL, hR, abs_of_nonneg (Nat.cast_nonneg ℓ),
      max_eq_left (by linarith : (0 : ℝ) ≤ p - 1)]
    have h3 : (ℓ : ℝ) ^ (p - 1) * (ℓ : ℝ) = (ℓ : ℝ) ^ ((p - 1) + 1) := by
      rw [Real.rpow_add hℓR, Real.rpow_one]
    rw [h3]
    congr 1
    ring

end PercLib.CriticalLRP.TreeExpansion

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.TreeExpansion.path_one_iff_subadd
#print axioms PercLib.CriticalLRP.TreeExpansion.subadd_iff_path_all
#print axioms PercLib.CriticalLRP.TreeExpansion.path_ell_homog
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_zero
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_one
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_two
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_three
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_hsub_not_subadd
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_not_three_homog
#print axioms PercLib.CriticalLRP.TreeExpansion.A₄_hsub_not_homog
#print axioms PercLib.CriticalLRP.TreeExpansion.path_rpow_le_sharp

/-! ## 5. The tree-free path closure `P_ℓ ≤ ℓ^(max p 1) * S^(ℓ-1) * Q`

The path decomposition of the marked leaf consumes exactly one analytic inequality: for a
nonnegative kernel `T` on a finite abelian `V` with row sums `S = ∑_y T y` and weighted first
moment `Q = ∑_y A y ^ p * T y`,

  `∑_{u : Fin ℓ → V} A (∑_j u_j) ^ p * ∏_j T (u_j) ≤ ℓ^(max p 1) * S^(ℓ-1) * Q`.

(`PathWeightedTreeSum` states this as `P_ℓ ≤ ℓ^(max p 1) * S^(ℓ-1) * Q` in a comment but does not
compile it.)  The content is: rewrite `P_ℓ` as `ℓ` copies of the same sum by moving the `j`-th
factor of the product onto the path increment, and then apply `path_rpow_le` coordinatewise. -/

namespace PercLib.CriticalLRP.TreeExpansion

open Finset

variable {V : Type*} [AddCommGroup V]

section PathClosure

variable [Fintype V]

/-- **The tree-free path closure.**  For a finite abelian `V`, a nonnegative weight `A` with
`A 0 = 0` that is subadditive, a nonnegative kernel `T`, real `p ≥ 0` and `1 ≤ ℓ`:
`P_ℓ ≤ ℓ^(max p 1) * S^(ℓ-1) * Q`. -/
theorem path_conv_le {A : V → ℝ} (hA0 : ∀ a : V, 0 ≤ A a) (h0 : A 0 = 0)
    (hA : ∀ a b : V, A (a + b) ≤ A a + A b) {p : ℝ} (hp : 0 ≤ p)
    {T : V → ℝ} (hT0 : ∀ y : V, 0 ≤ T y) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (∑ u : Fin ℓ → V, A (∑ j, u j) ^ p * ∏ j, T (u j))
      ≤ (ℓ : ℝ) ^ (max p 1) *
          ((∑ y : V, T y) ^ (ℓ - 1) * ∑ y : V, A y ^ p * T y) := by
  classical
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  -- Peeling the `j`-th factor of the product off: both sides equal the same explicit product.
  have hpt : ∀ (j : Fin ℓ) (u : Fin ℓ → V),
      A (u j) ^ p * ∏ i, T (u i)
        = ∏ i, (if i = j then A (u i) ^ p * T (u i) else T (u i)) := by
    intro j u
    have hR : (∏ i : Fin ℓ, (if i = j then A (u i) ^ p * T (u i) else T (u i)))
        = (A (u j) ^ p * T (u j)) * ∏ i ∈ (Finset.univ.erase j), T (u i) := by
      rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin ℓ))
        (fun i => if i = j then A (u i) ^ p * T (u i) else T (u i)) (Finset.mem_univ j)]
      simp only [ite_true]
      congr 1
      refine Finset.prod_congr rfl (fun i hi => ?_)
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [hij]
    have hL : A (u j) ^ p * ∏ i, T (u i)
        = (A (u j) ^ p * T (u j)) * ∏ i ∈ (Finset.univ.erase j), T (u i) := by
      rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin ℓ)) (fun i => T (u i))
        (Finset.mem_univ j)]
      ring
    rw [hR, hL]
  -- For each `j`, the `j`-th slice of `P_ℓ` is `Q * S^(ℓ-1)`.
  have hfib : ∀ j : Fin ℓ,
      (∑ u : Fin ℓ → V, A (u j) ^ p * ∏ i, T (u i))
        = (∑ y : V, A y ^ p * T y) * (∑ y : V, T y) ^ (ℓ - 1) := by
    intro j
    have hstep1 : ∀ u : Fin ℓ → V, A (u j) ^ p * ∏ i, T (u i)
        = ∏ i, (if i = j then A (u i) ^ p * T (u i) else T (u i)) := hpt j
    simp only [hstep1]
    rw [← Fintype.prod_sum (fun i : Fin ℓ => fun y : V =>
      if i = j then A y ^ p * T y else T y)]
    have hsumi : ∀ i : Fin ℓ,
        (∑ y : V, (if i = j then A y ^ p * T y else T y))
          = (if i = j then (∑ y : V, A y ^ p * T y) else (∑ y : V, T y)) := by
      intro i
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    simp only [hsumi]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin ℓ))
      (fun i => if i = j then (∑ y : V, A y ^ p * T y) else (∑ y : V, T y))
      (Finset.mem_univ j)]
    simp only [ite_true]
    congr 1
    have hconst : (∏ x ∈ (Finset.univ.erase j),
        (if x = j then (∑ y : V, A y ^ p * T y) else (∑ y : V, T y)))
        = ∏ _x ∈ (Finset.univ.erase j), (∑ y : V, T y) := by
      refine Finset.prod_congr rfl (fun x hx => ?_)
      have hxj : x ≠ j := Finset.ne_of_mem_erase hx
      simp [hxj]
    rw [hconst, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
  -- Pointwise bound and summation.
  have hstep : ∀ u : Fin ℓ → V,
      A (∑ j, u j) ^ p * ∏ j, T (u j)
        ≤ (ℓ : ℝ) ^ (max (p - 1) 0) * ((∑ j, A (u j) ^ p) * ∏ j, T (u j)) := by
    intro u
    have h1 := path_rpow_le hA0 h0 hA hp hℓ u
    have h2 : (0 : ℝ) ≤ ∏ j, T (u j) := Finset.prod_nonneg (fun j _ => hT0 (u j))
    calc A (∑ j, u j) ^ p * ∏ j, T (u j)
        ≤ ((ℓ : ℝ) ^ (max (p - 1) 0) * ∑ j, A (u j) ^ p) * ∏ j, T (u j) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = (ℓ : ℝ) ^ (max (p - 1) 0) * ((∑ j, A (u j) ^ p) * ∏ j, T (u j)) := by ring
  have hmax : max (p - 1) 0 + 1 = max p 1 := by
    by_cases hp1 : (1 : ℝ) ≤ p
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p - 1), max_eq_left hp1]; ring
    · push Not at hp1
      rw [max_eq_right (by linarith : p - 1 ≤ 0), max_eq_right hp1.le]; norm_num
  have hsplit : (ℓ : ℝ) ^ (max p 1) = (ℓ : ℝ) ^ (max (p - 1) 0) * (ℓ : ℝ) := by
    rw [← hmax, Real.rpow_add hℓR, Real.rpow_one]
  calc (∑ u : Fin ℓ → V, A (∑ j, u j) ^ p * ∏ j, T (u j))
      ≤ ∑ u : Fin ℓ → V,
          (ℓ : ℝ) ^ (max (p - 1) 0) * ((∑ j, A (u j) ^ p) * ∏ j, T (u j)) :=
        Finset.sum_le_sum (fun u _ => hstep u)
    _ = (ℓ : ℝ) ^ (max (p - 1) 0) *
          ∑ u : Fin ℓ → V, ((∑ j, A (u j) ^ p) * ∏ j, T (u j)) := by
        rw [Finset.mul_sum]
    _ = (ℓ : ℝ) ^ (max (p - 1) 0) *
          ∑ u : Fin ℓ → V, ∑ j : Fin ℓ, A (u j) ^ p * ∏ i, T (u i) := by
        congr 1
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.sum_mul]
    _ = (ℓ : ℝ) ^ (max (p - 1) 0) *
          ∑ j : Fin ℓ, ∑ u : Fin ℓ → V, A (u j) ^ p * ∏ i, T (u i) := by
        congr 1
        exact Finset.sum_comm
    _ = (ℓ : ℝ) ^ (max (p - 1) 0) *
          ∑ _j : Fin ℓ, ((∑ y : V, A y ^ p * T y) * (∑ y : V, T y) ^ (ℓ - 1)) := by
        congr 1
        exact Finset.sum_congr rfl (fun j _ => hfib j)
    _ = (ℓ : ℝ) ^ (max p 1) * ((∑ y : V, T y) ^ (ℓ - 1) * ∑ y : V, A y ^ p * T y) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsplit]
        ring

end PathClosure

end PercLib.CriticalLRP.TreeExpansion

#print axioms PercLib.CriticalLRP.TreeExpansion.path_conv_le

namespace PercLib.CriticalLRP.TreeExpansion

open Finset

variable {V : Type*} [AddCommGroup V]

section

variable [Fintype V]

/-- **The normalised path moment (the form the tree sum actually consumes).**  For a probability
kernel `ν` on a finite abelian group, a nonnegative subadditive `A` with `A 0 = 0`, real `p ≥ 0`
and `1 ≤ ℓ`, the `ℓ`-fold moment is at most `ℓ^(max p 1)` times the one-fold moment.  In the
campaign's notation with `B = A^p` and `ν = T / S` this is exactly `E_ℓ B ≤ ℓ^(max p 1) * E_1 B`,
the inequality to which the whole marked-leaf target reduces once the tree powers of `S` cancel.
Dropping `S` makes it directly consumable by the depth census `∑_ℓ C_ℓ ℓ^(max p 1) ≤ M (n-1)
n^(max p 1)`: there the only remaining inputs are the counts `C_ℓ`. -/
theorem path_moment_le {A : V → ℝ} (hA0 : ∀ a : V, 0 ≤ A a) (h0 : A 0 = 0)
    (hA : ∀ a b : V, A (a + b) ≤ A a + A b) {p : ℝ} (hp : 0 ≤ p)
    {ν : V → ℝ} (hν0 : ∀ y : V, 0 ≤ ν y) (hν1 : (∑ y : V, ν y) = 1)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (∑ u : Fin ℓ → V, A (∑ j, u j) ^ p * ∏ j, ν (u j))
      ≤ (ℓ : ℝ) ^ (max p 1) * ∑ y : V, A y ^ p * ν y := by
  have h := path_conv_le hA0 h0 hA hp hν0 hℓ
  rw [hν1, one_pow, one_mul] at h
  exact h

end

/-! ### The discrete-metric weight: a concrete, non-vacuous inhabitant

`A y = 1` off the origin and `A 0 = 0` is the discrete metric on `V`; it is nonnegative,
subadditive, has `A 0 = 0`, and is not identically zero.  So the source-faithful hypothesis set is
inhabited by a genuine *metric* weight with no additive-functional structure at all — which is
exactly what the earlier `φ : V →+ ℝ` formulation could not express (every additive functional on
a finite group vanishes). -/

/-- The discrete metric weight on an additive group. -/
def discW [DecidableEq V] (y : V) : ℝ := if y = 0 then 0 else 1

theorem discW_nonneg [DecidableEq V] (y : V) : 0 ≤ discW y := by
  unfold discW
  split <;> norm_num

theorem discW_zero [DecidableEq V] : discW (0 : V) = 0 := by
  unfold discW
  simp

theorem discW_subadd [DecidableEq V] (a b : V) : discW (a + b) ≤ discW a + discW b := by
  unfold discW
  by_cases ha : a = 0
  · subst ha
    rw [zero_add]
    by_cases hb : b = 0
    · subst hb; simp
    · simp [hb]
  · by_cases hb : b = 0
    · subst hb
      rw [add_zero]
      simp [ha]
    · by_cases hab : a + b = 0
      · simp [ha, hb, hab]
      · simp [ha, hb, hab]

end PercLib.CriticalLRP.TreeExpansion

#print axioms PercLib.CriticalLRP.TreeExpansion.path_moment_le
#print axioms PercLib.CriticalLRP.TreeExpansion.discW_nonneg
#print axioms PercLib.CriticalLRP.TreeExpansion.discW_zero
#print axioms PercLib.CriticalLRP.TreeExpansion.discW_subadd

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [DecidableEq V] [Fintype V] [AddCommGroup V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The path closure for the actual two-point function of the repository.**

With `T y = twoPoint pr ends o y` and `S = clusterVolume pr ends o` this is literally
`P_ℓ ≤ ℓ^(max p 1) * S^(ℓ-1) * Q` for the source's own objects: only `0 ≤ pr ≤ 1` and the strict
weight hypothesis `A 0 = 0`, `A ≥ 0`, `A` subadditive are used.  No `S ≥ 1`, no symmetry, no
translation invariance, and no tree combinatorics enter. -/
theorem path_conv_le_twoPoint (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) {A : V → ℝ} (hA0 : ∀ a : V, 0 ≤ A a) (h0 : A 0 = 0)
    (hA : ∀ a b : V, A (a + b) ≤ A a + A b) {p : ℝ} (hp0 : 0 ≤ p) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (∑ u : Fin ℓ → V, A (∑ j, u j) ^ p * ∏ j, twoPoint pr ends o (u j))
      ≤ (ℓ : ℝ) ^ (max p 1) * (clusterVolume pr ends o) ^ (ℓ - 1) *
          ∑ y : V, A y ^ p * twoPoint pr ends o y := by
  have h := path_conv_le (T := fun y => twoPoint pr ends o y) hA0 h0 hA hp0
    (fun y => twoPoint_nonneg hp hp1 ends o y) hℓ
  simp only [clusterVolume]
  exact h.trans_eq (by ring)

end PercLib.CriticalLRP.TreeExpansion

#print axioms PercLib.CriticalLRP.TreeExpansion.path_conv_le_twoPoint
