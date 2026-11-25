/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The marked-leaf path functional, from ordinary subadditivity

Stage 1 of the source-faithful marked-leaf estimate: the analytic core.

For a weight `A : V → ℝ` with `A 0 = 0`, `0 ≤ A` and `A (a + b) ≤ A a + A b`, a kernel
`k` with `k a b = T (b - a)`, and `o : V` with `T (y - o) = T y` (which holds for the
two-point function by translation invariance), the `ℓ`-step marked path functional

  `ps T B ℓ o = ∑_{u : Fin ℓ → V} B (o + ∑ u) * ∏_j T (u_j)`,   `B = A ^ p`,

satisfies `ps T B ℓ o ≤ ℓ^(max p 1) * S^(ℓ-1) * Q`, where `S = ∑_y T y` and
`Q = ∑_y A y ^ p * T y`.

This is the estimate the source obtains from `(∑_m a_m)^p ≤ ℓ^(max (p-1) 0) ∑_m a_m^p`.
It is *not* obtainable from the two-term hypothesis `hsub` alone (see `A₄_path_fails`
in `PathWeightedTreeSum.lean`); the whole point is that the `ℓ` terms are handled in a
single application, never compounded level by level.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.PathWeightedTreeSum
public import PercLib.CriticalLRP.TreeExpansion.TreeSumRecursionFull

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option linter.deprecated false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-! ## 1. Isolating one coordinate of a product sum -/

/-- **Coordinate isolation.** In a sum over all functions `u : ι → V` of a product over the
coordinates, the `j`-th coordinate can be given an extra factor `g` at the price of
`(card ι - 1)` copies of the row sum `∑ T`. -/
theorem sum_pi_mul_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (T g : V → ℝ) (j : ι) :
    (∑ u : ι → V, g (u j) * ∏ i, T (u i))
      = (∑ y : V, g y * T y) * (∑ y : V, T y) ^ (Fintype.card ι - 1) := by
  classical
  set S : ℝ := ∑ y : V, T y with hS
  set G : ℝ := ∑ y : V, g y * T y with hG
  have key : ∀ u : ι → V, g (u j) * ∏ i, T (u i)
      = ∏ i, (if i = j then g (u i) * T (u i) else T (u i)) := by
    intro u
    have h1 : (∏ i, (if i = j then g (u i) * T (u i) else T (u i)))
        = ∏ i, (T (u i) * (if i = j then g (u i) else 1)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h : i = j
      · simp [h, mul_comm]
      · simp [h]
    rw [h1, Finset.prod_mul_distrib]
    have h2 : (∏ i, (if i = j then g (u i) else 1)) = g (u j) := by
      rw [show (∏ i : ι, (if i = j then g (u i) else 1))
            = ∏ i : ι, (if j = i then g (u i) else 1) from
          Finset.prod_congr rfl fun i _ => by simp only [eq_comm]]
      rw [Finset.prod_ite_eq]
      simp
    rw [h2, mul_comm]
  have hprod : ∀ i : ι, (∑ y : V, (if i = j then g y * T y else T y))
      = if i = j then G else S := by
    intro i
    by_cases h : i = j
    · simp [h, hG]
    · simp [h, hS]
  calc (∑ u : ι → V, g (u j) * ∏ i, T (u i))
      = ∑ u : ι → V, ∏ i, (if i = j then g (u i) * T (u i) else T (u i)) :=
        Finset.sum_congr rfl fun u _ => key u
    _ = ∏ i, ∑ y : V, (if i = j then g y * T y else T y) := by
        rw [show (∑ u : ι → V, ∏ i, (if i = j then g (u i) * T (u i) else T (u i)))
              = ∑ u ∈ (Fintype.piFinset fun _ => (Finset.univ : Finset V)),
                  ∏ i, (if i = j then g (u i) * T (u i) else T (u i)) from by
            rw [Fintype.piFinset_univ]]
        exact (Finset.prod_univ_sum (fun _ => (Finset.univ : Finset V))
          (fun i y => if i = j then g y * T y else T y)).symm
    _ = ∏ i, (if i = j then G else S) := by
        exact Finset.prod_congr rfl fun i _ => hprod i
    _ = G * S ^ (Fintype.card ι - 1) := by
        have hmem : j ∈ (Finset.univ : Finset ι) := Finset.mem_univ j
        rw [← Finset.prod_erase_mul (Finset.univ : Finset ι)
          (fun i => if i = j then G else S) hmem]
        have h1 : (∏ x ∈ (Finset.univ : Finset ι).erase j, (if x = j then G else S)) = S ^ (Fintype.card ι - 1) := by
          rw [show (∏ x ∈ (Finset.univ : Finset ι).erase j, (if x = j then G else S))
                = ∏ x ∈ (Finset.univ : Finset ι).erase j, S from
              Finset.prod_congr rfl fun x hx => by
                rw [ite_eq_right (Finset.ne_of_mem_erase hx)]]
          rw [Finset.prod_const, Finset.card_erase_of_mem hmem, Finset.card_univ]
        have h2 : (if j = j then G else S) = G := ite_eq_left rfl
        rw [h1, h2, mul_comm]

/-! ## 2. The path functional -/

/-- The marked-path functional: sum over the `ℓ` path increments of the weight of the
endpoint, times the product of the edge weights. -/
noncomputable def ps (T B : V → ℝ) (n : ℕ) (v : V) : ℝ :=
  ∑ u : Fin n → V, B (v + ∑ j, u j) * ∏ j, T (u j)

theorem ps_zero (T B : V → ℝ) (v : V) : ps T B 0 v = B v := by
  have h : ∀ u : Fin 0 → V, B (v + ∑ j, u j) * ∏ j, T (u j) = B v := by
    intro u
    have hs : (∑ j : Fin 0, u j) = 0 := Fin.sum_univ_zero u
    have hp : (∏ j : Fin 0, T (u j)) = 1 := Fin.prod_univ_zero _
    rw [hs, add_zero, hp, mul_one]
  rw [ps, Finset.sum_congr rfl (fun u _ => h u), Finset.sum_const, Finset.card_univ,
    Fintype.card_pi]
  simp

/-- Translation of `V` by a fixed element, as a permutation. -/
def shiftEquiv (v : V) : V ≃ V where
  toFun y := v + y
  invFun y := y - v
  left_inv y := by show v + y - v = y; abel
  right_inv y := by show v + (y - v) = y; abel

/-- The unique splitting of `Fin (n+1) → V` into the first value and the tail. -/
def finConsEquiv (n : ℕ) : (Fin (n + 1) → V) ≃ (V × (Fin n → V)) where
  toFun u := (u 0, fun i => u i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv u := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]
  right_inv p := by
    have h1 : (Fin.cons p.1 p.2 : Fin (n + 1) → V) 0 = p.1 := Fin.cons_zero _ _
    have h2 : (fun i => (Fin.cons p.1 p.2 : Fin (n + 1) → V) i.succ) = p.2 := by
      funext i; exact Fin.cons_succ _ _ i
    simp only [h1, h2]

/-- The one-step recursion of the path functional. -/
theorem ps_succ (T B : V → ℝ) (n : ℕ) (v : V) :
    ps T B (n + 1) v = ∑ y : V, T y * ps T B n (v + y) := by
  rw [ps]
  rw [Fintype.sum_equiv (finConsEquiv (V := V) n)
    (fun u : Fin (n + 1) → V => B (v + ∑ j, u j) * ∏ j, T (u j))
    (fun p : V × (Fin n → V) => B (v + p.1 + ∑ j, p.2 j) * (T p.1 * ∏ j, T (p.2 j))) ?_]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ps, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  · intro u
    have h1 : (v + ∑ j, (u : Fin (n + 1) → V) j) = v + u 0 + ∑ j : Fin n, u j.succ := by
      rw [Fin.sum_univ_succ]; abel
    have h2 : (∏ j : Fin (n + 1), T (u j)) = T (u 0) * ∏ j : Fin n, T (u j.succ) :=
      Fin.prod_univ_succ _
    show B (v + ∑ j, u j) * ∏ j, T (u j)
      = B (v + u 0 + ∑ j : Fin n, u j.succ) * (T (u 0) * ∏ j : Fin n, T (u j.succ))
    rw [h1, h2]

/-- **The recursion in kernel form**: `ps (ℓ+1) v = ∑_w k v w * ps ℓ w` whenever
`k a b = T (b - a)`. -/
theorem ps_succ_kernel (k : V → V → ℝ) (T B : V → ℝ) (hk : ∀ a b : V, k a b = T (b - a))
    (n : ℕ) (v : V) :
    ps T B (n + 1) v = ∑ w : V, k v w * ps T B n w := by
  rw [ps_succ]
  exact Fintype.sum_equiv (shiftEquiv v)
    (fun y : V => T y * ps T B n (v + y))
    (fun w : V => k v w * ps T B n w)
    (fun y => by
      show T y * ps T B n (v + y) = k v (v + y) * ps T B n (v + y)
      rw [hk v (v + y), add_sub_cancel_left])

/-! ## 3. The `ℓ`-term bound from ordinary subadditivity -/

/-- `(k:ℝ) ^ max p 1 = k * (k:ℝ) ^ max (p-1) 0` for `k ≥ 1`. -/
theorem natCast_rpow_max {k : ℕ} (hk : 1 ≤ k) (p : ℝ) :
    (k : ℝ) ^ (max p 1) = (k : ℝ) * (k : ℝ) ^ (max (p - 1) 0) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rcases lt_or_ge p 1 with h | h
  · rw [max_eq_right h.le, max_eq_right (by linarith : p - 1 ≤ 0), Real.rpow_zero, mul_one,
      Real.rpow_one]
  · rw [max_eq_left h, max_eq_left (by linarith : (0 : ℝ) ≤ p - 1)]
    have hp : p = 1 + (p - 1) := by ring
    rw [hp, Real.rpow_add hk0, Real.rpow_one]
    ring

/-- **The marked-path estimate from ordinary subadditivity.**

`ps T (A^p) (ℓ) o ≤ ℓ^(max p 1) * S^(ℓ-1) * Q` for `ℓ ≥ 1`, where `S = ∑ T` and
`Q = ∑_y A y ^ p * T y`, under `A 0 = 0`, `0 ≤ A`, `A (a+b) ≤ A a + A b`, `0 ≤ T` and the
periodicity `T (y - o) = T y` of the two-point function at `o`. -/
theorem ps_bound (T : V → ℝ) (A : V → ℝ) (o : V)
    (hA0 : ∀ a : V, 0 ≤ A a) (h0 : A 0 = 0) (hsub : ∀ a b : V, A (a + b) ≤ A a + A b)
    (hT0 : ∀ y : V, 0 ≤ T y) (hper : ∀ y : V, T (y - o) = T y)
    {p : ℝ} (hp : 0 ≤ p) (m : ℕ) :
    ps T (fun y => A y ^ p) (m + 1) o
      ≤ ((m + 1 : ℕ) : ℝ) ^ (max p 1) * (∑ y : V, T y) ^ m * (∑ y : V, A y ^ p * T y) := by
  classical
  set S : ℝ := ∑ y : V, T y with hS
  set Q : ℝ := ∑ y : V, A y ^ p * T y with hQ
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun y _ => hT0 y
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun y _ =>
    mul_nonneg (Real.rpow_nonneg (hA0 y) p) (hT0 y)
  -- coordinate isolation, in the two shapes needed
  have hcoord : ∀ (j : Fin (m + 1)) (g : V → ℝ),
      (∑ u : Fin (m + 1) → V, g (u j) * ∏ i, T (u i)) = (∑ y : V, g y * T y) * S ^ m := by
    intro j g
    rw [sum_pi_mul_prod]
    simp [S, Fintype.card_fin]
  -- the shift `A (o + y)` may be removed from the first coordinate
  have hshift : (∑ y : V, A (o + y) ^ p * T y) = Q := by
    rw [hQ]
    refine Fintype.sum_equiv (shiftEquiv o)
      (fun y : V => A (o + y) ^ p * T y) (fun z : V => A z ^ p * T z) ?_
    intro y
    show A (o + y) ^ p * T y = A (o + y) ^ p * T (o + y)
    have hTy : T y = T (o + y) := by
      rw [← hper (o + y), add_sub_cancel_left]
    rw [hTy]
  -- termwise bound with the `ℓ`-term estimate applied once
  have hstep : ∀ u : Fin (m + 1) → V,
      A (o + ∑ j, u j) ^ p
        ≤ ((m + 1 : ℕ) : ℝ) ^ (max (p - 1) 0) *
            ∑ j : Fin (m + 1), A ((Fin.cons (o + u 0) (fun i => u i.succ) :
              Fin (m + 1) → V) j) ^ p := by
    intro u
    have hsum : (∑ j : Fin (m + 1),
        (Fin.cons (o + u 0) (fun i => u i.succ) : Fin (m + 1) → V) j) = o + ∑ j, u j := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      abel
    rw [← hsum]
    have := path_rpow_le (A := A) hA0 h0 hsub hp (ℓ := m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) (Fin.cons (o + u 0) (fun i => u i.succ))
    simpa using this
  have hj0 : (∑ u : Fin (m + 1) → V,
      A ((Fin.cons (o + u 0) (fun i => u i.succ) : Fin (m + 1) → V) 0) ^ p *
        ∏ i, T (u i)) = Q * S ^ m := by
    simp only [Fin.cons_zero]
    rw [hcoord 0 (fun y => A (o + y) ^ p), hshift]
  have hjs : ∀ i : Fin m, (∑ u : Fin (m + 1) → V,
      A ((Fin.cons (o + u 0) (fun i => u i.succ) : Fin (m + 1) → V) i.succ) ^ p *
        ∏ i, T (u i)) = Q * S ^ m := by
    intro i
    simp only [Fin.cons_succ]
    rw [hcoord i.succ (fun y => A y ^ p), ← hQ]
  rw [ps]
  have hmove : ∀ u : Fin (m + 1) → V,
      (((m + 1 : ℕ) : ℝ) ^ (max (p - 1) 0) *
          ∑ j : Fin (m + 1), A ((Fin.cons (o + u 0) (fun i => u i.succ) :
            Fin (m + 1) → V) j) ^ p) * ∏ i, T (u i)
        = ((m + 1 : ℕ) : ℝ) ^ (max (p - 1) 0) *
            ∑ j : Fin (m + 1),
              A ((Fin.cons (o + u 0) (fun i => u i.succ) :
                Fin (m + 1) → V) j) ^ p * ∏ i, T (u i) := by
    intro u
    rw [mul_assoc, Finset.sum_mul]
  calc (∑ u : Fin (m + 1) → V, A (o + ∑ j, u j) ^ p * ∏ i, T (u i))
      ≤ ∑ u : Fin (m + 1) → V,
          (((m + 1 : ℕ) : ℝ) ^ (max (p - 1) 0) *
            ∑ j : Fin (m + 1), A ((Fin.cons (o + u 0) (fun i => u i.succ) :
              Fin (m + 1) → V) j) ^ p) * ∏ i, T (u i) :=
        Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_right (hstep u) (Finset.prod_nonneg fun i _ => hT0 (u i))
    _ = ((m + 1 : ℕ) : ℝ) ^ (max (p - 1) 0) *
          ∑ j : Fin (m + 1), ∑ u : Fin (m + 1) → V,
            A ((Fin.cons (o + u 0) (fun i => u i.succ) : Fin (m + 1) → V) j) ^ p *
              ∏ i, T (u i) := by
        rw [Finset.sum_congr rfl fun u _ => hmove u]
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm
    _ = ((m + 1 : ℕ) : ℝ) ^ (max (p - 1) 0) *
          (Q * S ^ m + (m : ℝ) * (Q * S ^ m)) := by
        rw [Fin.sum_univ_succ, hj0,
          Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hjs i,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((m + 1 : ℕ) : ℝ) ^ (max p 1) * S ^ m * Q := by
        rw [natCast_rpow_max (Nat.succ_le_succ (Nat.zero_le m)) p]
        push_cast
        ring

end PercLib.CriticalLRP.TreeExpansion


/-
# The marked-leaf factorization of the tree weight

Stage 2 of the source-faithful marked-leaf estimate.

`treeSum` averages `RTree.wt` over all plane leaf-labelled trees, `wt` summing over the
values at the internal vertices.  Marking the leaf `i₀` and putting a weight `B` on the
value at that leaf, the whole tree weight factors as

  `∑_{y} B (y q) * wt k t y v = S ^ (2 * #leaves - 1 - ℓ) * ps T B ℓ v`,

where `ℓ = depth t q` is the number of vertices on the root–`q` path, `S = ∑_y k v y` is
the (constant) row sum and `ps` is the path functional of `PathCore.lean`.  Everything off
the path contributes the row sum `S` once per edge-plus-root factor, so the `2 * #leaves - 1`
factors of a tree with `#leaves` leaves split as `(2 * #leaves - 1 - ℓ) + ℓ`.

Together with `ps_bound` (which consumes ordinary subadditivity of `A` **once**, at length
`ℓ`) and `markedEdge_factor` this gives the marked-leaf estimate with the exponent `2n-2`
exactly, and no step needing `S ≥ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option linter.deprecated false

namespace PercLib.CriticalLRP.TreeExpansion

open Finset

set_option linter.unusedVariables false

namespace RTree

variable {α : Type*} {V : Type*} [Fintype V] [AddCommGroup V] [DecidableEq V]

/-! ## Auxiliary product-sum rearrangements -/

/-- The two-fold product-sum rearrangement used at every branching vertex. -/
theorem sum_sum_sum_factor {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : V → ℝ) (A₁ : ι → V → ℝ) (A₂ : κ → V → ℝ) :
    (∑ i, ∑ j, ∑ w : V, f w * A₁ i w * A₂ j w)
      = ∑ w : V, f w * ((∑ i, A₁ i w) * (∑ j, A₂ j w)) := by
  have h1 : ∀ i, (∑ j, ∑ w : V, f w * A₁ i w * A₂ j w)
      = ∑ w : V, ∑ j, f w * A₁ i w * A₂ j w := fun i => Finset.sum_comm
  calc (∑ i, ∑ j, ∑ w : V, f w * A₁ i w * A₂ j w)
      = ∑ i, ∑ w : V, ∑ j, f w * A₁ i w * A₂ j w :=
        Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ w : V, ∑ i, ∑ j, f w * A₁ i w * A₂ j w := Finset.sum_comm
    _ = ∑ w : V, f w * ((∑ i, A₁ i w) * (∑ j, A₂ j w)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        have h2 : ∀ i, (∑ j, f w * A₁ i w * A₂ j w) = (f w * A₁ i w) * (∑ j, A₂ j w) := by
          intro i
          rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl fun i _ => h2 i, ← Finset.sum_mul, ← Finset.mul_sum]
        exact mul_assoc _ _ _

/-- Every leaf hangs at distance at least one from the root. -/
theorem one_le_depth : ∀ (t : RTree α) (q : LeafPos t), 1 ≤ depth t q
  | leaf _, _ => le_refl 1
  | node l r, Sum.inl q => by
      have := one_le_depth l q
      show 1 ≤ depth l q + 1
      omega
  | node l r, Sum.inr q => by
      have := one_le_depth r q
      show 1 ≤ depth r q + 1
      omega

/-- The path functional at length one. -/
theorem ps_one (T B : V → ℝ) (v : V) : ps T B 1 v = ∑ y : V, B (v + y) * T y := by
  have h2 : ps T B (0 + 1) v = ∑ y : V, T y * ps T B 0 (v + y) := ps_succ T B 0 v
  simp only [ps_zero] at h2
  rw [zero_add] at h2
  rw [h2]
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _

/-! ## The marked-leaf factorization -/

/-- **The marked-leaf factorization of the tree weight.**

With `B` on the value at the marked leaf `q` and the kernel written `k a b = T (b - a)`,
the sum over all leaf values of the tree weight is the row sum `S` to the power
`2 * #leaves - 1 - depth t q`, times the path functional of length `depth t q`. -/
theorem sum_wt_marked (k : V → V → ℝ) (T B : V → ℝ)
    (hk : ∀ a b : V, k a b = T (b - a)) (S : ℝ) (hS : ∀ v : V, ∑ y : V, k v y = S) :
    ∀ (t : RTree α) (q : LeafPos t) (v : V),
      (∑ y : LeafPos t → V, B (y q) * wt k t y v)
        = S ^ (2 * t.numLeaves - 1 - depth t q) * ps T B (depth t q) v := by
  intro t
  induction t with
  | leaf a =>
    intro q v
    cases q
    have : Unique (LeafPos (leaf a)) := inferInstanceAs (Unique PUnit)
    have hL : (∑ y : LeafPos (leaf a) → V, B (y ⟨⟩) * wt k (leaf a) y v)
        = ∑ z : V, B z * k v z := by
      refine Fintype.sum_equiv (Equiv.funUnique (LeafPos (leaf a)) V)
        (fun y : LeafPos (leaf a) → V => B (y ⟨⟩) * wt k (leaf a) y v)
        (fun z : V => B z * k v z) ?_
      intro y
      show B (y ⟨⟩) * wt k (leaf a) y v = B (y ⟨⟩) * k v (y ⟨⟩)
      rw [show wt k (leaf a) y v = k v (y ⟨⟩) from rfl]
    have hk2 : (∑ z : V, B z * k v z) = ∑ y : V, B (v + y) * T y := by
      rw [← Fintype.sum_equiv (shiftEquiv v)
        (fun y : V => B (v + y) * T y)
        (fun z : V => B z * k v z)
        (fun y => ?_)]
      show B (v + y) * T y = B (v + y) * k v (v + y)
      rw [hk v (v + y), add_sub_cancel_left]
    have hd : (2 * (leaf a).numLeaves - 1 - (leaf a).depth (⟨⟩ : LeafPos (leaf a))) = 0 := by
      simp [numLeaves_leaf, depth]
    have hps : ps T B ((leaf a).depth (⟨⟩ : LeafPos (leaf a))) v = ∑ y : V, B (v + y) * T y := by
      rw [show (leaf a).depth (⟨⟩ : LeafPos (leaf a)) = 1 from rfl]
      exact ps_one T B v
    rw [hL, hk2, hd, hps, pow_zero, one_mul]
  | node l r ihl ihr =>
    intro q v
    have hnl : 1 ≤ l.numLeaves := numLeaves_pos l
    have hnr : 1 ≤ r.numLeaves := numLeaves_pos r
    rcases q with q' | q'
    · -- the marked leaf lies in the left subtree
      have hL : (∑ y : LeafPos (node l r) → V, B (y (Sum.inl q')) * wt k (node l r) y v)
          = ∑ w : V, k v w *
              ((∑ y1 : LeafPos l → V, B (y1 q') * wt k l y1 w) *
                (∑ y2 : LeafPos r → V, wt k r y2 w)) := by
        have hsplit : (∑ y : LeafPos (node l r) → V,
            B (y (Sum.inl q')) * wt k (node l r) y v)
            = ∑ y1 : LeafPos l → V, ∑ y2 : LeafPos r → V, ∑ w : V,
                k v w * (B (y1 q') * wt k l y1 w) * wt k r y2 w := by
          calc (∑ y : LeafPos (node l r) → V, B (y (Sum.inl q')) * wt k (node l r) y v)
              = ∑ y : LeafPos (node l r) → V, ∑ w : V,
                  B (y (Sum.inl q')) *
                    (k v w * wt k l (fun p => y (Sum.inl p)) w *
                      wt k r (fun p => y (Sum.inr p)) w) := by
                refine Finset.sum_congr rfl fun y _ => ?_
                simp only [wt]
                rw [Finset.mul_sum]
            _ = ∑ p : (LeafPos l → V) × (LeafPos r → V), ∑ w : V,
                  B (p.1 q') *
                    (k v w * wt k l p.1 w * wt k r p.2 w) := by
                refine Fintype.sum_equiv
                  (Equiv.sumArrowEquivProdArrow (LeafPos l) (LeafPos r) V) _ _ ?_
                intro y
                rfl
            _ = ∑ y1 : LeafPos l → V, ∑ y2 : LeafPos r → V, ∑ w : V,
                  B (y1 q') * (k v w * wt k l y1 w * wt k r y2 w) :=
                Fintype.sum_prod_type _
            _ = ∑ y1 : LeafPos l → V, ∑ y2 : LeafPos r → V, ∑ w : V,
                  k v w * (B (y1 q') * wt k l y1 w) * wt k r y2 w := by
                refine Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ =>
                  Finset.sum_congr rfl fun w _ => ?_
                ring
        rw [hsplit, sum_sum_sum_factor]
      rw [hL]
      have step1 : (∑ w : V, k v w *
            ((∑ y1 : LeafPos l → V, B (y1 q') * wt k l y1 w) *
              (∑ y2 : LeafPos r → V, wt k r y2 w)))
          = ∑ w : V, k v w *
              ((S ^ (2 * l.numLeaves - 1 - depth l q') * ps T B (depth l q') w) *
                S ^ (2 * r.numLeaves - 1)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [ihl q' w, sum_wt k S hS r w]
      rw [step1]
      have step2 : (∑ w : V, k v w *
            ((S ^ (2 * l.numLeaves - 1 - depth l q') * ps T B (depth l q') w) *
              S ^ (2 * r.numLeaves - 1)))
          = (S ^ (2 * l.numLeaves - 1 - depth l q') * S ^ (2 * r.numLeaves - 1)) *
              (∑ w : V, k v w * ps T B (depth l q') w) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring
      rw [step2, ← ps_succ_kernel k T B hk (depth l q') v]
      have hstep : depth (node l r) (Sum.inl q') = depth l q' + 1 := rfl
      have hidx : 2 * (node l r).numLeaves - 1 - (depth l q' + 1)
          = (2 * l.numLeaves - 1 - depth l q') + (2 * r.numLeaves - 1) := by
        have hlel : depth l q' ≤ 2 * l.numLeaves - 1 := by
          have := depth_le_numLeaves l q'
          omega
        rw [numLeaves_node]
        omega
      rw [hstep, hidx, pow_add]
    · -- the marked leaf lies in the right subtree
      have hL : (∑ y : LeafPos (node l r) → V, B (y (Sum.inr q')) * wt k (node l r) y v)
          = ∑ w : V, k v w *
              ((∑ y1 : LeafPos l → V, wt k l y1 w) *
                (∑ y2 : LeafPos r → V, B (y2 q') * wt k r y2 w)) := by
        have hsplit : (∑ y : LeafPos (node l r) → V,
            B (y (Sum.inr q')) * wt k (node l r) y v)
            = ∑ y1 : LeafPos l → V, ∑ y2 : LeafPos r → V, ∑ w : V,
                k v w * wt k l y1 w * (B (y2 q') * wt k r y2 w) := by
          calc (∑ y : LeafPos (node l r) → V, B (y (Sum.inr q')) * wt k (node l r) y v)
              = ∑ y : LeafPos (node l r) → V, ∑ w : V,
                  B (y (Sum.inr q')) *
                    (k v w * wt k l (fun p => y (Sum.inl p)) w *
                      wt k r (fun p => y (Sum.inr p)) w) := by
                refine Finset.sum_congr rfl fun y _ => ?_
                simp only [wt]
                rw [Finset.mul_sum]
            _ = ∑ p : (LeafPos l → V) × (LeafPos r → V), ∑ w : V,
                  B (p.2 q') *
                    (k v w * wt k l p.1 w * wt k r p.2 w) := by
                refine Fintype.sum_equiv
                  (Equiv.sumArrowEquivProdArrow (LeafPos l) (LeafPos r) V) _ _ ?_
                intro y
                rfl
            _ = ∑ y1 : LeafPos l → V, ∑ y2 : LeafPos r → V, ∑ w : V,
                  B (y2 q') * (k v w * wt k l y1 w * wt k r y2 w) :=
                Fintype.sum_prod_type _
            _ = ∑ y1 : LeafPos l → V, ∑ y2 : LeafPos r → V, ∑ w : V,
                  k v w * wt k l y1 w * (B (y2 q') * wt k r y2 w) := by
                refine Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ =>
                  Finset.sum_congr rfl fun w _ => ?_
                ring
        rw [hsplit, sum_sum_sum_factor]
      rw [hL]
      have step1 : (∑ w : V, k v w *
            ((∑ y1 : LeafPos l → V, wt k l y1 w) *
              (∑ y2 : LeafPos r → V, B (y2 q') * wt k r y2 w)))
          = ∑ w : V, k v w *
              (S ^ (2 * l.numLeaves - 1) *
                (S ^ (2 * r.numLeaves - 1 - depth r q') * ps T B (depth r q') w)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [ihr q' w, sum_wt k S hS l w]
      rw [step1]
      have step2 : (∑ w : V, k v w *
            (S ^ (2 * l.numLeaves - 1) *
              (S ^ (2 * r.numLeaves - 1 - depth r q') * ps T B (depth r q') w)))
          = (S ^ (2 * l.numLeaves - 1) * S ^ (2 * r.numLeaves - 1 - depth r q')) *
              (∑ w : V, k v w * ps T B (depth r q') w) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring
      rw [step2, ← ps_succ_kernel k T B hk (depth r q') v]
      have hstep : depth (node l r) (Sum.inr q') = depth r q' + 1 := rfl
      have hidx : 2 * (node l r).numLeaves - 1 - (depth r q' + 1)
          = (2 * l.numLeaves - 1) + (2 * r.numLeaves - 1 - depth r q') := by
        have hler : depth r q' ≤ 2 * r.numLeaves - 1 := by
          have := depth_le_numLeaves r q'
          omega
        rw [numLeaves_node]
        omega
      rw [hstep, hidx, pow_add]

end RTree

namespace RTree

variable {V : Type*} [Fintype V] [AddCommGroup V] [DecidableEq V]

/-- The same factorization with the leaf values parametrised by `Fin n` through the
bijection `leafOfPos`, which is how `treeSum` presents them. -/
theorem sum_wt_marked_labelled (k : V → V → ℝ) (T B : V → ℝ)
    (hk : ∀ a b : V, k a b = T (b - a)) (S : ℝ) (hS : ∀ v : V, ∑ y : V, k v y = S)
    {n : ℕ} {t : RTree (Fin n)} (ht : FullyLabelled t) (q : LeafPos t) (v : V) :
    (∑ x : Fin n → V, B (x (leafOfPos t q)) * wt k t (fun r => x (leafOfPos t r)) v)
      = S ^ (2 * n - 1 - depth t q) * ps T B (depth t q) v := by
  classical
  have hbij : Function.Bijective (leafOfPos t) :=
    ⟨leafOfPos_injective ht.1,
      fun a => exists_leafOfPos t a (mem_leaves_of_fullyLabelled ht a)⟩
  have hlen : t.numLeaves = n := by
    have h := ht.2
    rw [Fintype.card_fin] at h
    exact h
  set e := Equiv.ofBijective (leafOfPos t) hbij
  have hYX : (∑ x : Fin n → V, B (x (leafOfPos t q)) *
      wt k t (fun r => x (leafOfPos t r)) v)
      = ∑ y : LeafPos t → V, B (y q) * wt k t y v := by
    refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl V)).symm
      (fun x : Fin n → V => B (x (leafOfPos t q)) *
        wt k t (fun r => x (leafOfPos t r)) v)
      (fun y : LeafPos t → V => B (y q) * wt k t y v) ?_
    intro x
    rfl
  rw [hYX, sum_wt_marked k T B hk S hS t q v, hlen]

end RTree

end PercLib.CriticalLRP.TreeExpansion

/-
# The marked-leaf tree-sum estimate for all `n`, from ordinary subadditivity

This file assembles the source-faithful estimate

  `∑_x A (x i₀)^p * treeSum (twoPoint pr ends) n o x
      ≤ M (n-1) * n^(max p 1) * (clusterVolume pr ends o)^(2n-2)
          * ∑_y A y ^ p * twoPoint pr ends o y`

from `A 0 = 0`, `0 ≤ A` and `A (a+b) ≤ A a + A b` (ordinary subadditivity, no two-term
`hsub`, no additive `φ`, no `S ≥ 1` step).

The proof is the composition of
* `RTree.sum_wt_marked_labelled` — the marked leaf at depth `ℓ` splits the tree weight into
  `S^(2n-1-ℓ)` times the path functional of length `ℓ`;
* `ps_bound` — the path functional is `≤ ℓ^(max p 1) S^(ℓ-1) Q`, one application of the
  `ℓ`-term estimate `path_rpow_le` (this is where ordinary subadditivity is consumed);
* `markedEdge_factor` — `S^(2n-1-ℓ) S^(ℓ-1) = S^(2n-2)` exactly;
* `RTree.depth_le_of_fullyLabelled` — `ℓ ≤ n`, and `RTree.card_LT_fin_le` for the count.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option linter.deprecated false

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

namespace RTree

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- **The marked-leaf estimate for a single tree.** -/
theorem wt_marked_le (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (A : V → ℝ) (hA0 : ∀ y : V, 0 ≤ A y) (hA0' : A 0 = 0)
    (hsub : ∀ a b : V, A (a + b) ≤ A a + A b)
    {p : ℝ} (hpp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (i₀ : Fin n)
    (t : RTree.LT (Fin n)) :
    (∑ x : Fin n → V, A (x i₀) ^ p * wt (twoPoint pr ends) t.val
        (fun r => x (leafOfPos t.val r)) o)
      ≤ (n : ℝ) ^ (max p 1) * (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, A y ^ p * twoPoint pr ends o y := by
  classical
  set S : ℝ := clusterVolume pr ends o with hSdef
  set T : V → ℝ := fun y => twoPoint pr ends o y with hTdef
  set Q : ℝ := ∑ y : V, A y ^ p * twoPoint pr ends o y with hQdef
  have hSrow : ∀ v : V, ∑ y : V, twoPoint pr ends v y = S := by
    intro v
    rw [hSdef, clusterVolume]
    exact twoPoint_total_eq pr ends o hinv v
  have hT0 : ∀ y : V, 0 ≤ T y := fun y => twoPoint_nonneg hp hp1 ends o y
  have hper : ∀ y : V, T (y - o) = T y := by
    intro y
    rw [hTdef]
    exact (hinv o y).symm
  have hk : ∀ a b : V, twoPoint pr ends a b = T (b - a) := by
    intro a b
    rw [hTdef]
    exact hinv a b
  have hS0 : 0 ≤ S := by
    rw [hSdef, clusterVolume]
    exact Finset.sum_nonneg fun y _ => hT0 y
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact Finset.sum_nonneg fun y _ => mul_nonneg (Real.rpow_nonneg (hA0 y) p) (hT0 y)
  have hTsum : (∑ y : V, T y) = S := by
    rw [hTdef, hSdef, clusterVolume]
  have hQT : (∑ y : V, A y ^ p * T y) = Q := by
    rw [hTdef, hQdef]
  obtain ⟨q, hq⟩ := exists_leafOfPos t.val i₀ (mem_leaves_of_fullyLabelled t.2 i₀)
  have hfac : (∑ x : Fin n → V, A (x i₀) ^ p * wt (twoPoint pr ends) t.val
      (fun r => x (leafOfPos t.val r)) o)
      = S ^ (2 * n - 1 - depth t.val q) * ps T (fun y => A y ^ p) (depth t.val q) o := by
    have h := sum_wt_marked_labelled (twoPoint pr ends) T (fun y => A y ^ p)
      hk S hSrow t.2 q o
    rw [hq] at h
    exact h
  have hℓ1 : 1 ≤ depth t.val q := one_le_depth t.val q
  have hℓn : depth t.val q ≤ n := depth_le_of_fullyLabelled t.2 q
  have hℓ2 : depth t.val q ≤ 2 * n - 1 := by omega
  have hps := ps_bound T A o hA0 hA0' hsub hT0 hper (p := p) hpp (m := depth t.val q - 1)
  rw [Nat.sub_add_cancel hℓ1, hTsum, hQT] at hps
  have hstep : S ^ (2 * n - 1 - depth t.val q) *
      ps T (fun y => A y ^ p) (depth t.val q) o
      ≤ (n : ℝ) ^ (max p 1) * S ^ (2 * n - 2) * Q := by
    refine (mul_le_mul_of_nonneg_left hps (pow_nonneg hS0 _)).trans ?_
    have hedg : S ^ (2 * n - 1 - depth t.val q) * S ^ (depth t.val q - 1)
        = S ^ (2 * n - 2) := markedEdge_factor S hℓ1 hℓ2
    have hmono : ((depth t.val q : ℕ) : ℝ) ^ (max p 1) ≤ (n : ℝ) ^ (max p 1) :=
      rpow_max_le_of_le hℓn p
    have hpow : (0 : ℝ) ≤ S ^ (2 * n - 2) := pow_nonneg hS0 _
    rw [← hedg]
    calc S ^ (2 * n - 1 - depth t.val q) *
          (((depth t.val q : ℕ) : ℝ) ^ (max p 1) * S ^ (depth t.val q - 1) * Q)
        = ((depth t.val q : ℕ) : ℝ) ^ (max p 1) *
            (S ^ (2 * n - 1 - depth t.val q) * S ^ (depth t.val q - 1)) * Q := by ring
      _ ≤ (n : ℝ) ^ (max p 1) *
            (S ^ (2 * n - 1 - depth t.val q) * S ^ (depth t.val q - 1)) * Q := by
          refine mul_le_mul_of_nonneg_right ?_ hQ0
          exact mul_le_mul_of_nonneg_right hmono
            (mul_nonneg (pow_nonneg hS0 _) (pow_nonneg hS0 _))
  rw [hfac, hSdef, hQdef]
  exact hstep

end RTree

/-- **The marked-leaf tree-sum estimate, all `n ≥ 1`.**

This uses the algebraic hypothesis of the source: `A` is an arbitrary nonnegative subadditive
weight with `A 0 = 0`. On an infinite additive group this includes `A = |⟨·,u⟩|`; on the finite
groups treated here, metric weights give non-vacuous instances. It is not restricted to an additive
functional (which is identically zero on a finite group) and does not assume merely `hsub`. -/
theorem markedLeaf_treeSum_bound (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (A : V → ℝ) (hA0 : ∀ y : V, 0 ≤ A y) (hA0' : A 0 = 0)
    (hsub : ∀ a b : V, A (a + b) ≤ A a + A b)
    {p : ℝ} (hpp : 0 ≤ p) {n : ℕ} (hn : 1 ≤ n) (i₀ : Fin n) :
    (∑ x : Fin n → V, A (x i₀) ^ p * treeSum (twoPoint pr ends) n o x)
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max p 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, A y ^ p * twoPoint pr ends o y := by
  classical
  set S : ℝ := clusterVolume pr ends o with hSdef
  set Q : ℝ := ∑ y : V, A y ^ p * twoPoint pr ends o y with hQdef
  have hS0 : 0 ≤ S := by
    rw [hSdef, clusterVolume]
    exact Finset.sum_nonneg fun y _ => twoPoint_nonneg hp hp1 ends o y
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (Real.rpow_nonneg (hA0 y) p) (twoPoint_nonneg hp hp1 ends o y)
  have hc : (0 : ℝ) ≤ 1 / 2 ^ (n - 1) := by positivity
  have hrew : ∀ x : Fin n → V, A (x i₀) ^ p * treeSum (twoPoint pr ends) n o x
      = (1 / 2 ^ (n - 1)) * ∑ t : RTree.LT (Fin n),
          A (x i₀) ^ p * RTree.wt (twoPoint pr ends) t.val
            (fun r => x (RTree.leafOfPos t.val r)) o := by
    intro x
    rw [treeSum]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  calc (∑ x : Fin n → V, A (x i₀) ^ p * treeSum (twoPoint pr ends) n o x)
      = (1 / 2 ^ (n - 1)) * ∑ t : RTree.LT (Fin n), ∑ x : Fin n → V,
          A (x i₀) ^ p * RTree.wt (twoPoint pr ends) t.val
            (fun r => x (RTree.leafOfPos t.val r)) o := by
        rw [Finset.sum_congr rfl fun x _ => hrew x]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ (1 / 2 ^ (n - 1)) * ∑ _t : RTree.LT (Fin n),
          ((n : ℝ) ^ (max p 1) * S ^ (2 * n - 2) * Q) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) hc
        exact RTree.wt_marked_le pr hp hp1 ends o hinv A hA0 hA0' hsub hpp hn i₀ t
    _ = (1 / 2 ^ (n - 1)) *
          ((Fintype.card (RTree.LT (Fin n)) : ℝ) * ((n : ℝ) ^ (max p 1) * S ^ (2 * n - 2) * Q)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max p 1) * S ^ (2 * n - 2) * Q := by
        have hcard : (Fintype.card (RTree.LT (Fin n)) : ℝ)
            ≤ (2 : ℝ) ^ (n - 1) * (VolumeMoments.M (n - 1) : ℝ) := by
          have h := RTree.card_LT_fin_le n
          have h' : ((Fintype.card (RTree.LT (Fin n)) : ℝ)
              ≤ ((2 ^ (n - 1) * VolumeMoments.M (n - 1) : ℕ) : ℝ)) := by exact_mod_cast h
          rwa [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h'
        have hP : (0 : ℝ) ≤ (n : ℝ) ^ (max p 1) * S ^ (2 * n - 2) * Q :=
          mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg hS0 _)) hQ0
        have hbound : (1 / 2 ^ (n - 1)) *
            ((Fintype.card (RTree.LT (Fin n)) : ℝ) *
              ((n : ℝ) ^ (max p 1) * S ^ (2 * n - 2) * Q))
            ≤ (1 / 2 ^ (n - 1)) *
              (((2 : ℝ) ^ (n - 1) * (VolumeMoments.M (n - 1) : ℝ)) *
                ((n : ℝ) ^ (max p 1) * S ^ (2 * n - 2) * Q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hP) hc
        refine hbound.trans_eq ?_
        have h2 : (2 : ℝ) ^ (n - 1) ≠ 0 := by positivity
        field_simp
    _ = (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max p 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, A y ^ p * twoPoint pr ends o y := by
        rw [hSdef, hQdef]

end PercLib.CriticalLRP.TreeExpansion


/-
# The source-faithful replacement of `WeightedTreeSum`, and its consumer

`WeightedTreeSum` (in `SpatialTreeGraph.lean`) quantifies over an *additive* functional
`φ : V →+ ℝ` and the weight `|φ|^p`.  On a finite abelian group every such `φ` is zero
(`addMonoidHom_eq_zero_of_finite`), so for `p > 0` that hypothesis is vacuous — the
literal mathematical content the source uses is `A = |⟨·, u⟩|`, an arbitrary **subadditive**
nonnegative weight with `A 0 = 0`. The same algebraic hypothesis covers the source's inner-product
weights on an infinite additive group; finite-group non-vacuity is supplied by metric weights.

`WeightedTreeSumGen` below is the explicitly named source-faithful correction: `A` ranges
over all nonnegative subadditive weights with `A 0 = 0`.  `markedLeaf_treeSum_bound`
discharges it, and `weightedTreeSum_of_gen` shows it implies the old (vacuous) interface,
so nothing is lost.  `spatial_tree_graph_of_gen` and `spatial_tree_graph_of_bk_gen` are the
consumer forms of `spatial_tree_graph_of_inputs` / `spatial_tree_graph_of_bk` with the
artificial hypothesis replaced.  This is *not* the two-term `hsub` route: the whole point of
`markedLeaf_treeSum_bound` is that subadditivity is consumed once, at path length `ℓ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The source-faithful weighted-tree-sum input.**

The weight `A` is any nonnegative subadditive function with `A 0 = 0`. The source's inner-product
weights on an infinite additive group satisfy this algebraic hypothesis; on finite groups generic
metric weights qualify too. This replaces the vacuously satisfied `WeightedTreeSum`, which asks
the same for an additive `φ`. -/
def WeightedTreeSumGen (pr : E → ℝ) (ends : E → Sym2 V) (o : V) : Prop :=
  ∀ (n : ℕ) (_hn : 1 ≤ n) (i₀ : Fin n) (A : V → ℝ), (∀ y : V, 0 ≤ A y) → A 0 = 0 →
    (∀ a b : V, A (a + b) ≤ A a + A b) → ∀ (p : ℝ), 0 ≤ p →
    (∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) →
    (∑ x : Fin n → V, A (x i₀) ^ p * treeSum (twoPoint pr ends) n o x)
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max p 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, A y ^ p * twoPoint pr ends o y

/-- **The source-faithful weighted-tree-sum input holds**, for every finite abelian `V`,
every probability `pr` and every `ends`.  Discharged by `markedLeaf_treeSum_bound`. -/
theorem weightedTreeSumGen (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) : WeightedTreeSumGen pr ends o := by
  intro n hn i₀ A hA0 hA0' hsub p hpp hinv
  exact markedLeaf_treeSum_bound pr hp hp1 ends o hinv A hA0 hA0' hsub hpp hn i₀

/-- `y ↦ |φ y|` is a nonnegative subadditive weight with value `0` at `0`. -/
theorem abs_addMonoidHom_subadd (φ : V →+ ℝ) :
    (∀ y : V, 0 ≤ |φ y|) ∧ |φ 0| = 0 ∧ ∀ a b : V, |φ (a + b)| ≤ |φ a| + |φ b| := by
  refine ⟨fun y => abs_nonneg _, by simp, fun a b => ?_⟩
  rw [map_add]
  exact abs_add_le _ _

/-- **The old interface follows**: `WeightedTreeSumGen` implies the (vacuous) `WeightedTreeSum`.
So the correction only adds strength — the additive-functional form was never doing any
work for `p > 0`. -/
theorem weightedTreeSum_of_gen (pr : E → ℝ) (ends : E → Sym2 V) (o : V)
    (h : WeightedTreeSumGen pr ends o) : WeightedTreeSum pr ends o := by
  intro n hn i₀ φ p hp hinv
  exact h n hn i₀ (fun y => |φ y|) (abs_addMonoidHom_subadd φ).1
    (abs_addMonoidHom_subadd φ).2.1 (abs_addMonoidHom_subadd φ).2.2 p hp hinv

/-- **`lem:spatial_tree_graph` from the tree-graph inequality and the source-faithful
weighted-tree-sum input** — `spatial_tree_graph_of_inputs` with the artificial `WeightedTreeSum`
hypothesis replaced by `WeightedTreeSumGen`. -/
theorem spatial_tree_graph_of_gen (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (hW : WeightedTreeSumGen pr ends o)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (Φ : Fin n → V →+ ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, ∑ y : V, |Φ i y| ^ (∑ j, q j) * twoPoint pr ends o y ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, |Φ i (x i)| ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M :=
  spatial_tree_graph_of_inputs pr hp hp1 ends o hTG
    (weightedTreeSum_of_gen pr ends o hW) hinv hn q Φ M hq hP hM

/-- **The fully discharged consumer form**: both remaining inputs are available, the
tree-graph inequality from `BKIncreasing` and the weighted tree sum from
`weightedTreeSumGen`.  Nothing here is an assumption about the tree sum. -/
theorem spatial_tree_graph_of_bk_gen (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) (hBK : BKIncreasing pr)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (Φ : Fin n → V →+ ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, ∑ y : V, |Φ i y| ^ (∑ j, q j) * twoPoint pr ends o y ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, |Φ i (x i)| ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M :=
  spatial_tree_graph_of_gen pr hp hp1 ends o
    (PercLib.CriticalLRP.TreeGraph.treeGraphBound_of_bk' pr hp hp1 hBK)
    (weightedTreeSumGen pr hp hp1 ends o) hinv hn q Φ M hq hP hM

end PercLib.CriticalLRP.TreeExpansion

namespace PercLib.CriticalLRP.TreeExpansion
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSumGen
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSum_of_gen
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_of_gen
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_of_bk_gen
end PercLib.CriticalLRP.TreeExpansion

/-! ## Axiom audit — every theorem below depends only on
    `propext`, `Classical.choice`, `Quot.sound`. -/

namespace PercLib.CriticalLRP.TreeExpansion
#print axioms PercLib.CriticalLRP.TreeExpansion.sum_pi_mul_prod
#print axioms PercLib.CriticalLRP.TreeExpansion.ps_zero
#print axioms PercLib.CriticalLRP.TreeExpansion.ps_succ
#print axioms PercLib.CriticalLRP.TreeExpansion.ps_succ_kernel
#print axioms PercLib.CriticalLRP.TreeExpansion.natCast_rpow_max
#print axioms PercLib.CriticalLRP.TreeExpansion.ps_bound
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.ps_one
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.sum_sum_sum_factor
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.one_le_depth
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.sum_wt_marked
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.sum_wt_marked_labelled
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.wt_marked_le
#print axioms PercLib.CriticalLRP.TreeExpansion.markedLeaf_treeSum_bound
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSumGen
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSum_of_gen
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_of_gen
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_of_bk_gen
end PercLib.CriticalLRP.TreeExpansion
