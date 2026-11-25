/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 222 (Q-46), written on 2026-11-15 by PROVER-E. No upstream proof is
copied. Source of the statements: J. M. Hammersley and K. W. Morton (1954); N. Madras and
G. Slade, *The Self-Avoiding Walk* (1993), §1.2 (locators to be checked).
-/
module

public import Mathlib.Analysis.Subadditive
public import PercLib.Models.Lattice
public import PercLib.Percolation.Bond.SelfAvoiding

/-!
# Self-avoiding walks on `ℤ^d` and the connective constant

`c n` is the number of paths (self-avoiding walks) of length `n` from the origin of the
nearest-neighbour graph `zdGraph d`, written `Nat.card {p : Σ y, (zdGraph d).Path 0 y //
p.2.1.length = n}` (no new definition).

* `finite_paths_length`: these sets are finite.
* `card_paths_eq_card_paths_zero`: the count does not depend on the starting point.
* `card_paths_add_le`: `c (n + m) ≤ c n * c m` (cut a path after `n` steps and translate the
  second piece to the origin).
* `card_paths_succ_le`: `c (n + 1) ≤ 2d (2d - 1)^n`.
* `exists_tendsto_card_paths_rpow`: the connective constant `μ = lim c(n)^{1/n}` exists (Fekete),
  `1 ≤ μ ≤ 2d - 1`, and `μ ≤ c(n)^{1/n}` for every `n ≥ 1`.

This file adds no definition.
-/

@[expose] public section

open SimpleGraph Filter Topology

namespace PercLib.Models.Site

variable {d : ℕ}

/-- The degree bound of `ℤ^d`, with the locally finite structure given by finiteness. -/
theorem zdGraph_degree_le (x : Fin d → ℤ) [Fintype ((zdGraph d).neighborSet x)] :
    (zdGraph d).degree x ≤ 2 * d :=
  (zdGraph_degree d x).le

/-- **Finitely many paths of a given length.** -/
theorem finite_paths_length (d k : ℕ) (x : Fin d → ℤ) :
    Finite {p : Σ y, (zdGraph d).Path x y // p.2.1.length = k} := by
  classical
  let : (zdGraph d).LocallyFinite := fun v => (zdGraph_finite_neighborSet v).fintype
  cases k with
  | zero =>
    refine Finite.of_injective (β := {l : List (Fin d → ℤ) // l = []})
      (fun p => ⟨p.1.2.1.support.tail, ?_⟩) ?_
    · exact List.eq_nil_of_length_eq_zero (by rw [List.length_tail, Walk.length_support, p.2])
    · intro p p' h
      apply Subtype.ext
      apply PercLib.Percolation.Bond.path_tail_injective_in_graph (zdGraph d) x
      have := congrArg Subtype.val h
      exact this
  | succ n =>
    exact (PercLib.Percolation.Bond.finite_card_paths_length (zdGraph d)
      (fun v => zdGraph_degree_le v) x n).1

/-- Paths transported by a graph automorphism. -/
theorem card_paths_le_of_iso (φ : zdGraph d ≃g zdGraph d) (k : ℕ) (x : Fin d → ℤ) :
    Nat.card {p : Σ y, (zdGraph d).Path x y // p.2.1.length = k} ≤
      Nat.card {p : Σ y, (zdGraph d).Path (φ x) y // p.2.1.length = k} := by
  have := finite_paths_length d k (φ x)
  refine Nat.card_le_card_of_injective
    (fun p => ⟨⟨φ p.1.1, p.1.2.map φ.toHom φ.injective⟩, ?_⟩) ?_
  · change (p.1.2.1.map φ.toHom).length = k
    rw [Walk.length_map]
    exact p.2
  · intro p p' h
    apply Subtype.ext
    apply PercLib.Percolation.Bond.path_tail_injective_in_graph (zdGraph d) x
    have h1 := congrArg (fun z : {p : Σ y, (zdGraph d).Path (φ x) y // p.2.1.length = k} =>
      z.1.2.1.support.tail) h
    simp only at h1
    change (p.1.2.1.map φ.toHom).support.tail = (p'.1.2.1.map φ.toHom).support.tail at h1
    rw [Walk.support_map, Walk.support_map, ← List.map_tail, ← List.map_tail] at h1
    exact List.map_injective_iff.2 φ.injective h1

/-- **The number of paths does not depend on the starting point.** -/
theorem card_paths_eq_card_paths_zero (k : ℕ) (x : Fin d → ℤ) :
    Nat.card {p : Σ y, (zdGraph d).Path x y // p.2.1.length = k} =
      Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = k} := by
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_add (d := d) (-x)
  obtain ⟨ψ, hψ⟩ := exists_zdGraph_iso_add (d := d) x
  have h1 := card_paths_le_of_iso φ k x
  have h2 := card_paths_le_of_iso ψ k 0
  rw [hφ, add_neg_cancel] at h1
  rw [hψ, zero_add] at h2
  exact le_antisymm h1 h2

/-- A path is the first part of it followed by the rest. -/
theorem support_eq_take_append_drop {u v : Fin d → ℤ} (q : (zdGraph d).Walk u v) (n : ℕ) :
    q.support = (q.take n).support ++ (q.drop n).support.tail := by
  conv_lhs => rw [← Walk.append_take_drop_eq q n]
  rw [Walk.support_append]

/-- Cutting a path of length `n + m` after `n` steps gives a path of length `n` from the
origin, and a path of length `m` which, translated back to the origin, is again a path. -/
theorem exists_split_path (n m : ℕ)
    (p : {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n + m}) :
    ∃ a : {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n},
    ∃ b : {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = m},
      a.1.1 = p.1.2.1.getVert n ∧ a.1.2.1.support = (p.1.2.1.take n).support ∧
      b.1.2.1.support = (p.1.2.1.drop n).support.map (· + -(p.1.2.1.getVert n)) := by
  obtain ⟨⟨y, q⟩, hq⟩ := p
  simp only at hq ⊢
  refine ⟨⟨⟨q.1.getVert n, ⟨q.1.take n, q.2.take n⟩⟩, ?_⟩, ?_⟩
  · change (q.1.take n).length = n
    rw [Walk.take_length, hq]
    omega
  obtain ⟨φ, hφ⟩ := exists_zdGraph_iso_add (d := d) (-(q.1.getVert n))
  have h0 : φ (q.1.getVert n) = 0 := by rw [hφ, add_neg_cancel]
  refine ⟨⟨⟨φ y, ⟨((q.1.drop n).map φ.toHom).copy h0 rfl, ?_⟩⟩, ?_⟩, rfl, rfl, ?_⟩
  · rw [Walk.isPath_copy]
    exact (q.2.drop n).map φ.injective
  · change (((q.1.drop n).map φ.toHom).copy h0 rfl).length = m
    rw [Walk.length_copy, Walk.length_map, Walk.drop_length, hq]
    omega
  · change (((q.1.drop n).map φ.toHom).copy h0 rfl).support = _
    rw [Walk.support_copy, Walk.support_map]
    congr 1
    funext z
    exact hφ z

/-- **Submultiplicativity of the number of self-avoiding walks.** -/
theorem card_paths_add_le (d n m : ℕ) :
    Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n + m} ≤
      Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} *
        Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = m} := by
  have := finite_paths_length d n 0
  have := finite_paths_length d m 0
  rw [← Nat.card_prod]
  choose A B hA hB hC using exists_split_path (d := d) n m
  refine Nat.card_le_card_of_injective (fun p => (A p, B p)) fun p p' h => ?_
  have h1 := congrArg (fun z : {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} ×
    {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = m} => z.1.1.1) h
  have h2 := congrArg (fun z : {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} ×
    {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = m} => z.1.1.2.1.support) h
  have h3 := congrArg (fun z : {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} ×
    {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = m} => z.2.1.2.1.support) h
  simp only at h1 h2 h3
  rw [hA p, hA p'] at h1
  rw [hB p, hB p'] at h2
  rw [hC p, hC p'] at h3
  have hf : (fun x : Fin d → ℤ => x + -(p.1.2.1.getVert n)) =
      fun x => x + -(p'.1.2.1.getVert n) := by
    rw [h1]
  rw [hf] at h3
  have h3' := List.map_injective_iff.2 (add_left_injective (-(p'.1.2.1.getVert n))) h3
  have hs : p.1.2.1.support = p'.1.2.1.support := by
    rw [support_eq_take_append_drop p.1.2.1 n, support_eq_take_append_drop p'.1.2.1 n, h2, h3']
  apply Subtype.ext
  apply PercLib.Percolation.Bond.path_tail_injective_in_graph (zdGraph d) 0
  exact congrArg List.tail hs

/-- **Upper bound on the number of self-avoiding walks.** -/
theorem card_paths_succ_le (d n : ℕ) :
    Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n + 1} ≤
      2 * d * (2 * d - 1) ^ n := by
  let : (zdGraph d).LocallyFinite := fun v => (zdGraph_finite_neighborSet v).fintype
  exact (PercLib.Percolation.Bond.finite_card_paths_length (zdGraph d)
    (fun v => zdGraph_degree_le v) 0 n).2

/-- There is a self-avoiding walk of every length when `d ≥ 1`. -/
theorem one_le_card_paths (hd : 1 ≤ d) (n : ℕ) :
    1 ≤ Nat.card {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} := by
  have := finite_paths_length d n 0
  set i₀ : Fin d := ⟨0, hd⟩
  set y : Fin d → ℤ := Pi.single i₀ (n : ℤ)
  have hdist : (zdGraph d).dist 0 y = n := by
    rw [zdGraph_dist, Finset.sum_eq_single i₀]
    · simp [y]
    · intro j _ hj
      simp [y, hj]
    · simp
  obtain ⟨w, hw⟩ := ((zdGraph_connected d).preconnected 0 y).exists_walk_length_eq_dist
  have hpath := w.isPath_of_length_eq_dist hw
  have : Nonempty {p : Σ y, (zdGraph d).Path 0 y // p.2.1.length = n} :=
    ⟨⟨⟨y, ⟨w, hpath⟩⟩, by rw [← hdist]; exact hw⟩⟩
  exact Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩)

/-- **The connective constant of `ℤ^d`** (Fekete). `c(n)^{1/n}` converges to a limit `μ`
with `μ ≤ c(n)^{1/n}` for every `n ≥ 1` and `1 ≤ μ ≤ 2d - 1`. -/
theorem exists_tendsto_card_paths_rpow (hd : 1 ≤ d) :
    ∃ μ : ℝ, Tendsto (fun n : ℕ => (Nat.card {p : Σ y, (zdGraph d).Path 0 y //
        p.2.1.length = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) ∧
      (∀ n, n ≠ 0 → μ ≤ (Nat.card {p : Σ y, (zdGraph d).Path 0 y //
        p.2.1.length = n} : ℝ) ^ ((n : ℝ)⁻¹)) ∧
      1 ≤ μ ∧ μ ≤ 2 * d - 1 := by
  set u : ℕ → ℝ := fun n => (Nat.card {p : Σ y, (zdGraph d).Path 0 y //
    p.2.1.length = n} : ℝ)
  have hu0 : ∀ n, 0 ≤ u n := fun n => Nat.cast_nonneg _
  have hsub : Submultiplicative u := fun m n => by
    simp only [u]
    exact_mod_cast card_paths_add_le d m n
  refine ⟨hsub.lim, hsub.tendsto_lim hu0, fun n hn => hsub.lim_le_rpow hu0 hn, ?_, ?_⟩
  · refine ge_of_tendsto' (hsub.tendsto_lim hu0) fun n => Real.one_le_rpow ?_ (by positivity)
    have := one_le_card_paths hd n
    simp only [u]
    exact_mod_cast this
  · set a : ℝ := 2 * d
    set b : ℝ := 2 * d - 1
    have hb1 : 1 ≤ b := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      simp only [b]; linarith
    have hb0 : 0 < b := by linarith
    have ha0 : 0 < a := by simp only [a]; positivity
    have hlim : Tendsto (fun n : ℕ => (a / b) ^ (1 / ((n : ℝ) + 1)) * b) atTop (𝓝 b) := by
      have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have hc : Tendsto (fun x : ℝ => (a / b) ^ x) (𝓝 0) (𝓝 ((a / b) ^ (0 : ℝ))) :=
        Real.continuousAt_const_rpow (div_pos ha0 hb0).ne'
      rw [Real.rpow_zero] at hc
      simpa using (hc.comp h0).mul_const b
    have hbound : ∀ n : ℕ, hsub.lim ≤ (a / b) ^ (1 / ((n : ℝ) + 1)) * b := by
      intro n
      have h1 := hsub.lim_le_rpow hu0 (Nat.succ_ne_zero n)
      have h2 : u (n + 1) ≤ a * b ^ n := by
        simp only [u, a, b]
        have := card_paths_succ_le d n
        have hcast : ((2 * d * (2 * d - 1) ^ n : ℕ) : ℝ) = 2 * d * (2 * d - 1) ^ n := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * d)]
          ring
        rw [← hcast]
        exact_mod_cast this
      have h3 : u (n + 1) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ (a * b ^ n) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (hu0 _) h2 (by positivity)
      have h4 : (a * b ^ n) ^ (((n + 1 : ℕ) : ℝ)⁻¹) = (a / b) ^ (1 / ((n : ℝ) + 1)) * b := by
        have hab : a * b ^ n = (a / b) * b ^ (n + 1) := by
          field_simp
          ring
        rw [hab, Real.mul_rpow (div_pos ha0 hb0).le (by positivity),
          Real.pow_rpow_inv_natCast hb0.le (Nat.succ_ne_zero n)]
        push_cast
        rw [one_div]
      exact h1.trans (h3.trans h4.le)
    exact ge_of_tendsto' hlim hbound

/-! ### Non-vacuity -/

/-- On `ℤ` the connective constant is `1`. -/
example : ∃ μ : ℝ, Tendsto (fun n : ℕ => (Nat.card {p : Σ y, (zdGraph 1).Path 0 y //
    p.2.1.length = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) ∧ μ = 1 := by
  obtain ⟨μ, hμ, -, h1, h2⟩ := exists_tendsto_card_paths_rpow (d := 1) le_rfl
  exact ⟨μ, hμ, le_antisymm (by norm_num at h2; exact h2) h1⟩

/-- In `ℤ²` there are at most `4 · 3²` self-avoiding walks of length `3`. -/
example : Nat.card {p : Σ y, (zdGraph 2).Path 0 y // p.2.1.length = 2 + 1} ≤ 4 * 3 ^ 2 :=
  card_paths_succ_le 2 2

end PercLib.Models.Site
