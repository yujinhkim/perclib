/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 225, Q-48, items 1 to 3). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.SelfAvoidingDecay

/-!
# Self-avoiding bounds for `τ` and `χ` with a length lower bound, and `ℤ^d`

On a graph `G` of maximal degree `Δ`, with a profile supported on `G` off the diagonal and at
most `p` on its edges:

* if every `G`-walk from `x` to `y ≠ x` has length at least `D`, then
  `τ(x, y) ≤ ∑_{n + 1 ≥ D} Δ (Δ - 1)^n p^{n+1}`;
* `χ(x) ≤ 1 + ∑_n Δ (Δ - 1)^n p^{n+1}`.

On `ℤ^d` (`zdGraph d`, the Hasse diagram of the product order) a walk from `x` to `y` has length
at least `‖y - x‖₁ = ∑ᵢ |yᵢ - xᵢ|`, which gives the `ℤ^d` two-point bound. Local finiteness and
the degree bound of `zdGraph d` are hypotheses here, as in `SelfAvoiding.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Open paths realise connections almost surely as `G`-paths whose edges are open. -/
theorem ae_exists_path_of_mem_conn [Countable V] (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) (x y : V) :
    ∀ᵐ ω ∂law q, ω ∈ conn x y → ∃ r : G.Path x y,
      (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω := by
  classical
  filter_upwards [ae_openGraph_le_of_zero_off_diagonal G q hoff] with ω hω hconn
  obtain ⟨w, hw⟩ := (hconn : (openGraph ω).Reachable x y).exists_isPath
  have hedG : ∀ e ∈ w.edges, e ∈ G.edgeSet := fun e he =>
    SimpleGraph.edgeSet_mono hω (w.edges_subset_edgeSet he)
  refine ⟨⟨w.transfer G hedG, hw.transfer hedG⟩, fun e he => ?_⟩
  simp only [SimpleGraph.Walk.edges_transfer, List.coe_toFinset, mem_ofPred_eq] at he
  have h1 := w.edges_subset_edgeSet he
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1
  exact h1.1

/-- The probability that a `G`-path of length `n + 1` is open is at most `p^{n+1}`. -/
theorem law_path_open_le (G : SimpleGraph V) (q : Sym2 V → unitInterval) (p : unitInterval)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p) {x y : V} (r : G.Path x y) {n : ℕ}
    (hr : r.1.length = n + 1) :
    law q {ω : Config V | (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} ≤
      (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1) := by
  classical
  rw [law, prodBernoulli_subset]
  calc _ ≤ ∏ _e ∈ r.1.edges.toFinset, (unitInterval.toNNReal p : ℝ≥0∞) :=
        Finset.prod_le_prod (fun e he => ENNReal.coe_le_coe.mpr
          (hle e (r.1.edges_subset_edgeSet (List.mem_toFinset.mp he))))
    _ = _ := by
        rw [Finset.prod_const, List.toFinset_card_of_nodup r.2.isTrail.edges_nodup,
          SimpleGraph.Walk.length_edges, hr]

/-- **Self-avoiding decay of `τ` with a length lower bound.** -/
theorem tau_le_of_degree_le_of_length_ge [Countable V] (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    {x y : V} (hxy : x ≠ y) {D : ℕ} (hD : ∀ w : G.Walk x y, D ≤ w.length) :
    tau q x y ≤ ∑' n : ℕ, if D ≤ n + 1 then
      (Δ : ℝ≥0∞) * ((Δ : ℝ≥0∞) - 1) ^ n * (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1) else 0 := by
  classical
  set E : ℕ → Set (Config V) := fun n =>
    if D ≤ n + 1 then {ω | ∃ y', ∃ r : G.Path x y', r.1.length = n + 1 ∧
      (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} else ∅ with hE
  have hsub : ∀ᵐ ω ∂law q, ω ∈ conn x y → ω ∈ ⋃ n, E n := by
    filter_upwards [ae_exists_path_of_mem_conn G q hoff x y] with ω hω hconn
    obtain ⟨r, hr⟩ := hω hconn
    have hlen : r.1.length ≠ 0 := fun h => hxy (SimpleGraph.Walk.eq_of_length_eq_zero h)
    obtain ⟨n, hn⟩ : ∃ n, r.1.length = n + 1 := ⟨r.1.length - 1, by omega⟩
    have hDn : D ≤ n + 1 := hn ▸ hD r.1
    refine mem_iUnion.2 ⟨n, ?_⟩
    simp only [hE, hDn, ite_true, mem_ofPred_eq]
    exact ⟨y, r, hn, hr⟩
  calc tau q x y ≤ law q (⋃ n, E n) := measure_mono_ae hsub
    _ ≤ ∑' n, law q (E n) := measure_iUnion_le _
    _ ≤ _ := by
      refine ENNReal.tsum_le_tsum fun n => ?_
      simp only [hE]
      split_ifs
      · refine (law_exists_path_length_le G hΔ q p hle x n).trans (le_of_eq ?_)
        push_cast
        rfl
      · simp

/-- **Susceptibility.** `χ(x) ≤ 1 + ∑_n Δ (Δ - 1)^n p^{n+1}`. -/
theorem chi_le_one_add_tsum_selfAvoiding [Countable V] (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    (x : V) :
    chi q x ≤ 1 + ∑' n : ℕ,
      (Δ : ℝ≥0∞) * ((Δ : ℝ≥0∞) - 1) ^ n * (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1) := by
  classical
  set P : ℕ → Type _ := fun n => {r : Σ y, G.Path x y // r.2.1.length = n + 1}
  set c : ℕ → ℝ≥0∞ := fun n => (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1)
  -- For `y ≠ x`, a connection to `y` is an open `G`-path of some length ending at `y`.
  have hτ : ∀ y, y ≠ x → tau q x y ≤ ∑' n, ∑' r : P n, if r.1.1 = y then c n else 0 := by
    intro y hyx
    set A : (n : ℕ) → P n → Set (Config V) := fun n r =>
      if r.1.1 = y then {ω | (r.1.2.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} else ∅
    have hsub : ∀ᵐ ω ∂law q, ω ∈ conn x y → ω ∈ ⋃ n, ⋃ r : P n, A n r := by
      filter_upwards [ae_exists_path_of_mem_conn G q hoff x y] with ω hω hconn
      obtain ⟨r, hr⟩ := hω hconn
      have hlen : r.1.length ≠ 0 := fun h => hyx (SimpleGraph.Walk.eq_of_length_eq_zero h).symm
      obtain ⟨n, hn⟩ : ∃ n, r.1.length = n + 1 := ⟨r.1.length - 1, by omega⟩
      refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨⟨⟨y, r⟩, hn⟩, ?_⟩⟩
      simp only [A, ite_true]
      exact hr
    have : ∀ n, Countable (P n) := fun n => (finite_card_paths_length G hΔ x n).1.to_countable
    calc tau q x y ≤ law q (⋃ n, ⋃ r : P n, A n r) := measure_mono_ae hsub
      _ ≤ ∑' n, law q (⋃ r : P n, A n r) := measure_iUnion_le _
      _ ≤ ∑' n, ∑' r : P n, law q (A n r) :=
          ENNReal.tsum_le_tsum fun n => measure_iUnion_le _
      _ ≤ _ := by
          refine ENNReal.tsum_le_tsum fun n => ENNReal.tsum_le_tsum fun r => ?_
          simp only [A]
          split_ifs
          · exact law_path_open_le G q p hle r.1.2 r.2
          · simp
  have hcount : ∀ n, ∑' r : P n, c n ≤ (Δ : ℝ≥0∞) * ((Δ : ℝ≥0∞) - 1) ^ n * c n := by
    intro n
    have hc := finite_card_paths_length G hΔ x n
    have : Finite (P n) := hc.1
    rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe]
    gcongr
    calc (Nat.card (P n) : ℝ≥0∞) ≤ ((Δ * (Δ - 1) ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast hc.2
      _ = _ := by push_cast; rfl
  rw [chi_eq_tsum_tau, ENNReal.tsum_eq_add_tsum_ite x, tau_self]
  gcongr
  calc ∑' y, (if y = x then 0 else tau q x y)
      ≤ ∑' y, ∑' n, ∑' r : P n, (if r.1.1 = y then c n else 0) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        split_ifs with h
        · exact bot_le
        · exact hτ y h
    _ = ∑' n, ∑' r : P n, ∑' y, (if r.1.1 = y then c n else 0) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun n => ENNReal.tsum_comm
    _ = ∑' n, ∑' _r : P n, c n := by
        refine tsum_congr fun n => tsum_congr fun r => ?_
        simp
    _ ≤ _ := ENNReal.tsum_le_tsum hcount

/-! ### `ℤ^d` -/

/-- A step of `zdGraph d` changes one coordinate by one. -/
theorem sum_natAbs_sub_eq_one_of_adj {d : ℕ} {u w : Fin d → ℤ}
    (h : (PercLib.Models.Site.zdGraph d).Adj u w) : ∑ i, (w i - u i).natAbs = 1 := by
  classical
  have key : ∀ a b : Fin d → ℤ, a ⋖ b → ∑ i, (b i - a i).natAbs = 1 := by
    intro a b hab
    obtain ⟨i, t, hit, rfl⟩ := Pi.covBy_iff_exists_right_eq.1 hab
    rw [Order.covBy_iff_add_one_eq] at hit
    rw [Finset.sum_eq_single i]
    · simp [← hit]
    · intro j _ hj
      simp [Function.update_of_ne hj]
    · simp
  rcases h with h | h
  · exact key u w h
  · rw [← key w u h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.natAbs_neg, neg_sub]

/-- A walk in `zdGraph d` from `x` to `y` has length at least `‖y - x‖₁`. -/
theorem sum_natAbs_sub_le_length {d : ℕ} {x y : Fin d → ℤ}
    (w : (PercLib.Models.Site.zdGraph d).Walk x y) : ∑ i, (y i - x i).natAbs ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.length_cons]
    calc ∑ i, (c i - a i).natAbs ≤ ∑ i, ((c i - b i).natAbs + (b i - a i).natAbs) :=
          Finset.sum_le_sum fun i _ => by
            have : c i - a i = (c i - b i) + (b i - a i) := by ring
            rw [this]
            exact Int.natAbs_add_le _ _
      _ = ∑ i, (c i - b i).natAbs + 1 := by
          rw [Finset.sum_add_distrib, sum_natAbs_sub_eq_one_of_adj hab]
      _ ≤ p.length + 1 := by omega

/-- **Two-point decay on `ℤ^d`.** -/
theorem tau_zd_le {d : ℕ} [(PercLib.Models.Site.zdGraph d).LocallyFinite]
    (hdegree : ∀ v, (PercLib.Models.Site.zdGraph d).degree v ≤ 2 * d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ (PercLib.Models.Site.zdGraph d).edgeSet → q e = 0)
    (hle : ∀ e ∈ (PercLib.Models.Site.zdGraph d).edgeSet, q e ≤ p)
    {x : Fin d → ℤ} (hx : x ≠ 0) :
    tau q 0 x ≤ ∑' n : ℕ, if ∑ i, (x i).natAbs ≤ n + 1 then
      ((2 * d : ℕ) : ℝ≥0∞) * (((2 * d : ℕ) : ℝ≥0∞) - 1) ^ n *
        (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1) else 0 :=
  tau_le_of_degree_le_of_length_ge _ hdegree q p hoff hle (Ne.symm hx) fun w => by
    simpa using sum_natAbs_sub_le_length w

end PercLib.Percolation.Bond

end
