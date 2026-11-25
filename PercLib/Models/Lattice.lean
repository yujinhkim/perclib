/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 192 (Q-32), written on 2026-11-15 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import PercLib.Models.Site.Basic

/-!
# The nearest-neighbour graph of `ℤ^d`

For `zdGraph d = SimpleGraph.hasse (Fin d → ℤ)`, with the `ℓ¹` distance
`N(x, y) = ∑ i, (y i - x i).natAbs`:

* adjacency is `N(x, y) = 1`, that is `y = x ± e_i` (`zdGraph_adj_iff`, `zdGraph_adj_iff_exists`);
* the graph is locally finite, of degree `2d` (`zdGraph_degree`);
* the graph distance is `N` and the graph is connected (`zdGraph_dist`, `zdGraph_connected`);
* balls are finite, with `2n + 1` points when `d = 1`;
* translations, coordinate permutations and coordinate sign changes are automorphisms.

This file adds no definition.
-/

@[expose] public section

open Finset

namespace PercLib.Models.Site

variable {d : ℕ}

/-- **Adjacency in `ℤ^d`, coordinate form.** Two vertices are adjacent when they differ by
one in exactly one coordinate. -/
theorem zdGraph_adj_iff_exists (x y : Fin d → ℤ) :
    (zdGraph d).Adj x y ↔
      ∃ i, (x i + 1 = y i ∨ y i + 1 = x i) ∧ ∀ j, j ≠ i → x j = y j := by
  rw [SimpleGraph.hasse_adj, Pi.covBy_iff, Pi.covBy_iff]
  simp only [Order.covBy_iff_add_one_eq]
  constructor
  · rintro (⟨i, hi, hj⟩ | ⟨i, hi, hj⟩)
    · exact ⟨i, Or.inl hi, hj⟩
    · exact ⟨i, Or.inr hi, fun j hji => (hj j hji).symm⟩
  · rintro ⟨i, hi | hi, hj⟩
    · exact Or.inl ⟨i, hi, hj⟩
    · exact Or.inr ⟨i, hi, fun j hji => (hj j hji).symm⟩

/-- Coordinates off `i` agree, so the `ℓ¹` distance is the `i`-th difference. -/
theorem l1_eq_of_eq_off (x y : Fin d → ℤ) (i : Fin d) (h : ∀ j, j ≠ i → x j = y j) :
    ∑ j, (y j - x j).natAbs = (y i - x i).natAbs := by
  refine Finset.sum_eq_single i (fun j _ hji => ?_) (by simp)
  rw [h j hji, sub_self, Int.natAbs_zero]

/-- **Adjacency in `ℤ^d` is `ℓ¹` distance one.** -/
theorem zdGraph_adj_iff_l1 (x y : Fin d → ℤ) :
    (zdGraph d).Adj x y ↔ ∑ i, (y i - x i).natAbs = 1 := by
  rw [zdGraph_adj_iff_exists]
  constructor
  · rintro ⟨i, hi, hj⟩
    rw [l1_eq_of_eq_off x y i hj]
    omega
  · intro h
    obtain ⟨i, -, hi⟩ : ∃ i ∈ (univ : Finset (Fin d)), (y i - x i).natAbs ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [Finset.sum_eq_zero hc] at h
      exact zero_ne_one h
    have hsplit := Finset.add_sum_erase univ (fun j => (y j - x j).natAbs) (mem_univ i)
    rw [h] at hsplit
    have hi1 : (y i - x i).natAbs = 1 := by omega
    have hrest : ∑ j ∈ univ.erase i, (y j - x j).natAbs = 0 := by omega
    rw [Finset.sum_eq_zero_iff] at hrest
    refine ⟨i, by omega, fun j hji => ?_⟩
    have := hrest j (mem_erase.2 ⟨hji, mem_univ j⟩)
    omega

/-- **Adjacency in `ℤ^d`** (`ℓ¹` form with absolute values, as in the issue). -/
theorem zdGraph_adj_iff (x y : Fin d → ℤ) :
    (zdGraph d).Adj x y ↔ ∑ i, |y i - x i| = 1 := by
  rw [zdGraph_adj_iff_l1]
  simp_rw [← Int.natCast_natAbs]
  exact_mod_cast Iff.rfl

/-- The neighbours of `x`: one step up or down in one coordinate. -/
theorem zdGraph_adj_iff_eq_update (x y : Fin d → ℤ) :
    (zdGraph d).Adj x y ↔
      ∃ p : Fin d × Bool, y = Function.update x p.1 (x p.1 + if p.2 then 1 else -1) := by
  rw [zdGraph_adj_iff_exists]
  constructor
  · rintro ⟨i, hi, hj⟩
    refine ⟨(i, decide (x i + 1 = y i)), ?_⟩
    funext j
    by_cases hji : j = i
    · subst hji
      rcases hi with hi | hi
      · simp [hi]
      · have : ¬ x j + 1 = y j := by omega
        simp only [Function.update_self, this, decide_false, Bool.false_eq_true, ite_false]
        omega
    · rw [Function.update_of_ne hji]
      exact (hj j hji).symm
  · rintro ⟨⟨i, b⟩, rfl⟩
    refine ⟨i, ?_, fun j hji => by rw [Function.update_of_ne hji]⟩
    cases b <;> simp

/-- The map from directions to neighbours is injective. -/
theorem injective_update_step (x : Fin d → ℤ) :
    Function.Injective fun p : Fin d × Bool =>
      Function.update x p.1 (x p.1 + if p.2 then 1 else -1) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hij : i = j := by
    by_contra hij
    have := congrFun h i
    simp only [Function.update_self, Function.update_of_ne hij] at this
    cases b <;> simp at this
  subst hij
  have := congrFun h i
  simp only [Function.update_self, add_right_inj] at this
  cases b <;> cases c <;> simp_all

/-- The neighbourhood of `x` is the range of the steps. -/
theorem zdGraph_neighborSet_eq (x : Fin d → ℤ) :
    (zdGraph d).neighborSet x =
      Set.range fun p : Fin d × Bool => Function.update x p.1 (x p.1 + if p.2 then 1 else -1) := by
  ext y
  rw [SimpleGraph.mem_neighborSet, zdGraph_adj_iff_eq_update]
  simp only [Set.mem_range, eq_comm]

/-- **The graph of `ℤ^d` is locally finite.** -/
theorem zdGraph_finite_neighborSet (x : Fin d → ℤ) : ((zdGraph d).neighborSet x).Finite := by
  rw [zdGraph_neighborSet_eq]
  exact Set.finite_range _

/-- **Every vertex of `ℤ^d` has degree `2d`.** -/
theorem zdGraph_degree (d : ℕ) (x : Fin d → ℤ) [Fintype ((zdGraph d).neighborSet x)] :
    (zdGraph d).degree x = 2 * d := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  rw [show (zdGraph d).neighborSet x = _ from zdGraph_neighborSet_eq x,
    Nat.card_range_of_injective (injective_update_step x)]
  simp [Nat.card_eq_fintype_card, mul_comm]

/-- One step changes the `ℓ¹` distance to a fixed vertex by at most one. -/
theorem l1_le_l1_add_one_of_adj {x x' : Fin d → ℤ} (h : (zdGraph d).Adj x x') (y : Fin d → ℤ) :
    ∑ i, (y i - x i).natAbs ≤ ∑ i, (y i - x' i).natAbs + 1 := by
  rw [← (zdGraph_adj_iff_l1 x x').1 h, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have : y i - x i = (y i - x' i) + (x' i - x i) := by ring
  rw [this]
  exact Int.natAbs_add_le _ _

/-- Every walk is at least as long as the `ℓ¹` distance of its ends. -/
theorem l1_le_length {x y : Fin d → ℤ} (w : (zdGraph d).Walk x y) :
    ∑ i, (y i - x i).natAbs ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c h w ih =>
    rw [SimpleGraph.Walk.length_cons]
    exact (l1_le_l1_add_one_of_adj h c).trans (by omega)

/-- There is a walk whose length is the `ℓ¹` distance. -/
theorem exists_walk_length_eq_l1 (x y : Fin d → ℤ) :
    ∃ w : (zdGraph d).Walk x y, w.length = ∑ i, (y i - x i).natAbs := by
  suffices h : ∀ n : ℕ, ∀ x : Fin d → ℤ, ∑ i, (y i - x i).natAbs = n →
      ∃ w : (zdGraph d).Walk x y, w.length = n from h _ x rfl
  intro n
  induction n with
  | zero =>
    intro x hx
    have hxy : x = y := by
      funext i
      have := (Finset.sum_eq_zero_iff.1 hx) i (mem_univ i)
      omega
    subst hxy
    exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
    intro x hx
    obtain ⟨i, -, hi⟩ : ∃ i ∈ (univ : Finset (Fin d)), (y i - x i).natAbs ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [Finset.sum_eq_zero hc] at hx
      exact Nat.zero_ne_add_one n hx
    set x' := Function.update x i (x i + if x i < y i then 1 else -1) with hx'
    have hadj : (zdGraph d).Adj x x' := (zdGraph_adj_iff_eq_update x x').2
      ⟨(i, decide (x i < y i)), by simp [hx']⟩
    have hsum : ∑ j, (y j - x j).natAbs = ∑ j, (y j - x' j).natAbs + 1 := by
      rw [← Finset.add_sum_erase univ _ (mem_univ i), ← Finset.add_sum_erase univ _ (mem_univ i)]
      have hrest : ∑ j ∈ univ.erase i, (y j - x j).natAbs =
          ∑ j ∈ univ.erase i, (y j - x' j).natAbs :=
        Finset.sum_congr rfl fun j hj => by
          rw [hx', Function.update_of_ne (ne_of_mem_erase hj)]
      rw [hrest, hx', Function.update_self]
      split_ifs <;> omega
    obtain ⟨w, hw⟩ := ih x' (by omega)
    exact ⟨SimpleGraph.Walk.cons hadj w, by rw [SimpleGraph.Walk.length_cons, hw]⟩

/-- **The graph of `ℤ^d` is connected**, for every `d`, including `d = 0`. -/
theorem zdGraph_connected (d : ℕ) : (zdGraph d).Connected :=
  (SimpleGraph.connected_iff _).2 ⟨fun x y => ⟨(exists_walk_length_eq_l1 x y).choose⟩,
    ⟨0⟩⟩

/-- **The graph distance of `ℤ^d` is the `ℓ¹` distance.** -/
theorem zdGraph_dist (d : ℕ) (x y : Fin d → ℤ) :
    (zdGraph d).dist x y = ∑ i, (y i - x i).natAbs := by
  obtain ⟨w, hw⟩ := exists_walk_length_eq_l1 x y
  obtain ⟨w', hw'⟩ := ((zdGraph_connected d).preconnected x y).exists_walk_length_eq_dist
  refine le_antisymm ?_ ?_
  · rw [← hw]; exact SimpleGraph.dist_le w
  · rw [← hw']; exact l1_le_length w'

/-- **Balls of `ℤ^d` are finite.** -/
theorem zdGraph_ball_finite (x : Fin d → ℤ) (n : ℕ) :
    {y | (zdGraph d).dist x y ≤ n}.Finite := by
  refine (Set.Finite.pi (t := fun i => Set.Icc (x i - n) (x i + n))
    fun i => Set.finite_Icc _ _).subset fun y hy => ?_
  simp only [Set.mem_ofPred_eq, zdGraph_dist] at hy
  have hle : ∀ i, (y i - x i).natAbs ≤ n := fun i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)).trans hy
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
  intro i
  have := hle i
  omega

/-- **In `ℤ`, the ball of radius `n` has `2n + 1` points.** -/
theorem zdGraph_one_ball_ncard (x : Fin 1 → ℤ) (n : ℕ) :
    {y | (zdGraph 1).dist x y ≤ n}.ncard = 2 * n + 1 := by
  have himg : (fun y : Fin 1 → ℤ => y 0) '' {y | (zdGraph 1).dist x y ≤ n} =
      Set.Icc (x 0 - n) (x 0 + n) := by
    ext a
    simp only [Set.mem_image, Set.mem_ofPred_eq, zdGraph_dist, Fin.sum_univ_one, Set.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩
      omega
    · intro ha
      exact ⟨fun _ => a, by simp only; omega, rfl⟩
  have hinj : Set.InjOn (fun y : Fin 1 → ℤ => y 0) {y | (zdGraph 1).dist x y ≤ n} :=
    fun y _ z _ h => funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h
  rw [← hinj.ncard_image, himg, Set.ncard_eq_toFinset_card', Set.toFinset_Icc,
    Int.card_Icc]
  omega

/-- Adjacency is determined by the coordinatewise differences. -/
theorem zdGraph_adj_iff_of_sub {x y x' y' : Fin d → ℤ}
    (h : ∀ i, ((y' i - x' i).natAbs = (y i - x i).natAbs)) :
    (zdGraph d).Adj x' y' ↔ (zdGraph d).Adj x y := by
  simp only [zdGraph_adj_iff_l1, h]

/-- **Translations are automorphisms of `ℤ^d`.** -/
theorem exists_zdGraph_iso_add (g : Fin d → ℤ) :
    ∃ φ : zdGraph d ≃g zdGraph d, ∀ x, φ x = x + g :=
  ⟨{ toEquiv := Equiv.addRight g
     map_rel_iff' := fun {x y} => zdGraph_adj_iff_of_sub fun i => by
       simp only [Equiv.coe_addRight, Pi.add_apply, add_sub_add_right_eq_sub] },
    fun _ => rfl⟩

/-- **Coordinate permutations are automorphisms of `ℤ^d`.** -/
theorem exists_zdGraph_iso_perm (σ : Equiv.Perm (Fin d)) :
    ∃ φ : zdGraph d ≃g zdGraph d, ∀ x, φ x = x ∘ σ := by
  refine ⟨{ toEquiv := (Equiv.arrowCongr σ.symm (Equiv.refl ℤ))
            map_rel_iff' := fun {x y} => ?_ }, fun x => ?_⟩
  · simp only [zdGraph_adj_iff_l1, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl,
      Function.comp_apply, id_eq]
    exact (Equiv.sum_comp σ (fun i => (y i - x i).natAbs)).symm ▸ Iff.rfl
  · funext i
    simp [Equiv.arrowCongr_apply]

/-- **Coordinate sign changes are automorphisms of `ℤ^d`.** -/
theorem exists_zdGraph_iso_neg (s : Fin d → Bool) :
    ∃ φ : zdGraph d ≃g zdGraph d, ∀ x i, φ x i = if s i then -x i else x i := by
  refine ⟨{ toEquiv := Equiv.piCongrRight fun i => if s i then Equiv.neg ℤ else Equiv.refl ℤ
            map_rel_iff' := fun {x y} => zdGraph_adj_iff_of_sub fun i => ?_ }, fun x i => ?_⟩
  · change ((if s i then Equiv.neg ℤ else Equiv.refl ℤ) (y i) -
      (if s i then Equiv.neg ℤ else Equiv.refl ℤ) (x i)).natAbs = (y i - x i).natAbs
    cases s i
    · rfl
    · simp only [ite_true, Equiv.neg_apply]
      rw [show -y i - -x i = -(y i - x i) by ring, Int.natAbs_neg]
  · change (if s i then Equiv.neg ℤ else Equiv.refl ℤ) (x i) = if s i then -x i else x i
    cases s i <;> rfl

/-! ### Non-vacuity -/

/-- `ℤ^0` is a single vertex of degree `0`; `ℤ` has degree `2`. -/
example : (∃ i : Fintype ((zdGraph 0).neighborSet 0), @SimpleGraph.degree _ (zdGraph 0) 0 i = 0) ∧
    ∃ i : Fintype ((zdGraph 1).neighborSet 0), @SimpleGraph.degree _ (zdGraph 1) 0 i = 2 :=
  ⟨⟨_, @zdGraph_degree 0 0 (zdGraph_finite_neighborSet 0).fintype⟩,
    ⟨_, @zdGraph_degree 1 0 (zdGraph_finite_neighborSet 0).fintype⟩⟩

/-- Two points of `ℤ²` at `ℓ¹` distance three. -/
example : (zdGraph 2).dist 0 ![1, -2] = 3 := by
  rw [zdGraph_dist]
  decide

end PercLib.Models.Site
