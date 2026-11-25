/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Extended-power arithmetic and the finite-fresh-set supremum

Swarm `smwpbvro2`, member m2, direction d2.

`epow lam n` (committed, `BFS.Defs`) is the supremum of the finite powers `lam ^ k`,
`k ≤ n`.  Here we collect the arithmetic needed by the generation induction —
subadditivity of the exponent, multiplicativity in the base, the value on a natural
number — and the reduction of the generation cardinality to a supremum of finite open
counts over the *fresh* queried set `E(A_k,U_k)`.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Generation.RowCharge

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators Topology

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*} [Countable V]

/-! ### `epow` arithmetic -/

theorem epow_one {lam : ℝ≥0∞} (hlam : 1 ≤ lam) : epow lam 1 = lam := by
  have h : epow lam 1 = epow lam ((1 : ℕ) : ℕ∞) := rfl
  rw [h, epow_natCast lam hlam 1, ENNReal.rpow_natCast, pow_one]

/-- Subadditivity of `epow` in the exponent. -/
theorem epow_add_le {lam : ℝ≥0∞} (hlam : 1 ≤ lam) (h0 : lam ≠ 0) (htop : lam ≠ ⊤)
    (a b : ℕ∞) : epow lam (a + b) ≤ epow lam a * epow lam b := by
  conv_lhs => rw [epow]
  refine iSup_le (fun k => ?_)
  set ka : ℕ∞ := a ⊓ (k : ℕ∞) with hka
  set kb : ℕ∞ := b ⊓ (k : ℕ∞) with hkb
  have hka_top : ka ≠ ⊤ := ne_top_of_le_ne_top (by simp) inf_le_right
  have hkb_top : kb ≠ ⊤ := ne_top_of_le_ne_top (by simp) inf_le_right
  have hkab_top : ka + kb ≠ ⊤ := by
    simp [hka_top, hkb_top]
  have h1 : ((a + b) ⊓ (k : ℕ∞)) ≤ ka + kb := by
    rw [hka, hkb]
    by_cases h : (k : ℕ∞) ≤ a
    · rw [show a ⊓ (k : ℕ∞) = (k : ℕ∞) from inf_eq_right.mpr h]
      exact inf_le_right.trans (le_add_of_nonneg_right (by simp : (0:ℕ∞) ≤ b ⊓ (k:ℕ∞)))
    · rw [show a ⊓ (k : ℕ∞) = a from inf_eq_left.mpr (lt_of_not_ge h).le]
      by_cases h2 : (k : ℕ∞) ≤ b
      · rw [show b ⊓ (k : ℕ∞) = (k : ℕ∞) from inf_eq_right.mpr h2]
        exact inf_le_right.trans (le_add_of_nonneg_left (by simp : (0:ℕ∞) ≤ a))
      · rw [show b ⊓ (k : ℕ∞) = b from inf_eq_left.mpr (lt_of_not_ge h2).le]
        exact inf_le_left
  have h2 : ((a + b) ⊓ (k : ℕ∞)).toNat ≤ (ka + kb).toNat :=
    ENat.toNat_le_toNat h1 hkab_top
  have h3 : (ka + kb).toNat = ka.toNat + kb.toNat :=
    ENat.toNat_add hka_top hkb_top
  calc lam ^ ((((a + b) ⊓ (k : ℕ∞))).toNat : ℝ)
      ≤ lam ^ (((ka + kb).toNat) : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le hlam (by exact_mod_cast h2)
    _ = lam ^ (((ka.toNat : ℝ) + (kb.toNat : ℝ))) := by rw [h3]; push_cast; ring_nf
    _ = lam ^ (ka.toNat : ℝ) * lam ^ (kb.toNat : ℝ) := ENNReal.rpow_add _ _ h0 htop
    _ ≤ epow lam a * epow lam b := by
        rw [epow, epow]
        exact mul_le_mul' (le_iSup (fun m : ℕ => lam ^ ((a ⊓ (m : ℕ∞)).toNat : ℝ)) k)
          (le_iSup (fun m : ℕ => lam ^ ((b ⊓ (m : ℕ∞)).toNat : ℝ)) k)

/-- Monotonicity of `epow` in the base, for bases at least one. -/
theorem epow_le_epow_base {x y : ℝ≥0∞} (hxy : x ≤ y) (n : ℕ∞) : epow x n ≤ epow y n := by
  rw [epow, epow]
  refine iSup_le (fun k => ?_)
  exact le_iSup_of_le k (ENNReal.rpow_le_rpow hxy (by positivity))

/-- Multiplicativity of `epow` in the base, as an inequality in the direction the
generation induction needs. -/
theorem epow_mul_le {x y : ℝ≥0∞} (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hxt : x ≠ ⊤) (hyt : y ≠ ⊤)
    (n : ℕ∞) : epow x n * epow y n ≤ epow (x * y) n := by
  rcases eq_or_ne n ⊤ with h | h
  · subst h
    rcases eq_or_lt_of_le hx1 with hx | hx
    · rw [← hx, epow_one_top, one_mul, one_mul]
    · rcases eq_or_lt_of_le hy1 with hy | hy
      · rw [← hy, epow_one_top, mul_one, mul_one]
      · rw [epow_top_of_one_lt x hx, epow_top_of_one_lt y hy,
          epow_top_of_one_lt (x * y) (one_lt_mul'' hx hy)]
        exact le_top
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (ENat.natCast_toNat h).symm⟩
    rw [epow_natCast x hx1 m, epow_natCast y hy1 m,
      epow_natCast (x * y) (one_le_mul hx1 hy1) m]
    rw [← ENNReal.mul_rpow_of_ne_top hxt hyt]

/-- `epow` on a finite cluster cardinality, in real form. -/
theorem epow_ofReal_pow {τ : ℝ} (hτ : 1 ≤ τ) (n : ℕ) :
    epow (ENNReal.ofReal τ) (n : ℕ∞) = ENNReal.ofReal (τ ^ n) := by
  rw [epow_natCast _ (by simpa using ENNReal.ofReal_le_ofReal hτ) n]
  rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by positivity), Real.rpow_natCast]

/-! ### Finite subsets of a set with prescribed cardinality -/

theorem exists_finset_card_le_encard {α : Type*} :
    ∀ {s : Set α} {n : ℕ}, (n : ℕ∞) ≤ s.encard →
      ∃ t : Finset α, (t : Set α) ⊆ s ∧ t.card = n := by
  intro s n
  induction n with
  | zero => intro _; exact ⟨∅, by simp, rfl⟩
  | succ n ih =>
    intro h
    classical
    have hn : ((n : ℕ∞)) ≤ s.encard := le_trans (by exact_mod_cast Nat.le_succ n) h
    obtain ⟨t, ht, htc⟩ := ih hn
    have hex : ∃ x ∈ s, x ∉ t := by
      by_contra hc
      have hsub : s ⊆ (t : Set α) := by
        intro y hy
        by_contra hyt
        exact hc ⟨y, hy, hyt⟩
      have hle : s.encard ≤ ((t : Set α)).encard := Set.encard_mono hsub
      have htcard : ((t : Set α)).encard = (t.card : ℕ∞) := by simp
      rw [htcard, htc] at hle
      have : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := le_trans h hle
      exact absurd this (by exact_mod_cast Nat.not_succ_le_self n)
    obtain ⟨x, hxs, hxt⟩ := hex
    refine ⟨insert x t, ?_, ?_⟩
    · intro y hy
      rw [Finset.mem_coe] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxs
      · exact ht (Finset.mem_coe.mpr hy)
    · rw [Finset.card_insert_of_notMem hxt, htc]

end PercLib.CriticalLRP.Exploration.BFS
