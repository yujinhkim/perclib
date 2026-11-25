/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 133 (Q-12), written on 2026-11-14 by PROVER-E, extending the path
sums of `PercLib.Percolation.Bond.RowSum`. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.RowSum
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Exponential decay in the support-graph distance under the row-sum condition

Let `Gq = SimpleGraph.fromEdgeSet {e | 0 < q e}` be the support graph of `q`. A simple path
that uses a pair with `q e = 0` contributes nothing to the path sum bounding `τ(x, y)`, and
every other path is a walk in `Gq`. So if every `Gq`-walk from `x` to `y` has length at
least `k`, only walks of length at least `k` contribute, and under a row-sum bound `m < 1`
this gives `τ(x, y) ≤ m ^ k (1 - m)⁻¹`. In particular `τ(x, y) ≤ m ^ d (1 - m)⁻¹` with `d`
the `Gq`-distance, and `τ(x, y) = 0` when `y` is not `Gq`-reachable from `x`. The same
bound holds for the part of the susceptibility carried by such `y`.

This file adds no definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal
open Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **Tail of the walk sums.** Under a row-sum bound `m < 1`, the masked walk sums of length
at least `k` total at most `m ^ k (1 - m)⁻¹`. -/
theorem tsum_walkSum_ge_le (a : V → V → ℝ≥0∞) (m : ℝ≥0∞)
    (hrow : ∀ v, ∑' w, offDiagonal a v w ≤ m) (_hm : m < 1) (k : ℕ) (v : V) :
    ∑' n, (if k ≤ n then walkSum (offDiagonal a) n v else 0) ≤ m ^ k * (1 - m)⁻¹ := by
  calc ∑' n, (if k ≤ n then walkSum (offDiagonal a) n v else 0)
      ≤ ∑' n, (if k ≤ n then m ^ n else 0) := ENNReal.tsum_le_tsum fun n => by
        split_ifs
        · exact walkSum_masked_le_pow a m hrow n v
        · exact le_rfl
    _ = ∑' j, m ^ (j + k) := by
        have hinj : Function.Injective fun j : ℕ => j + k := fun _ _ h => by simpa using h
        rw [← hinj.tsum_eq (f := fun n => if k ≤ n then m ^ n else 0)]
        · simp
        · intro n hn
          by_cases h : k ≤ n
          · exact ⟨n - k, Nat.sub_add_cancel h⟩
          · exact absurd (by simp [h]) hn
    _ = m ^ k * (1 - m)⁻¹ := by
        simp_rw [pow_add]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]

/-- A simple path all of whose pairs have positive probability is a walk in the support
graph of the same length. -/
theorem exists_support_walk_of_forall_pos (q : Sym2 V → unitInterval) {x y : V}
    (p : (⊤ : SimpleGraph V).Walk x y) (hpos : ∀ e ∈ p.edges, 0 < q e) :
    ∃ w : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Walk x y, w.length = p.length := by
  refine ⟨p.transfer _ fun e he => ?_, SimpleGraph.Walk.length_transfer _ _⟩
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨hpos e he, SimpleGraph.not_isDiag_of_mem_edgeSet _ (p.edges_subset_edgeSet he)⟩

/-- A path that is too short for the support graph has zero cylinder product. -/
theorem path_prod_eq_zero_of_length_lt (q : Sym2 V → unitInterval) {x y : V} {k : ℕ}
    (hk : ∀ p : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Walk x y, k ≤ p.length)
    (p : (⊤ : SimpleGraph V).Path x y) (hp : p.1.length < k) :
    ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) = 0 := by
  by_contra hne
  have hpos : ∀ e ∈ p.1.edges, 0 < q e := by
    intro e he
    by_contra hq
    have hq0 : q e = 0 := le_antisymm (not_lt.1 hq) (q e).2.1
    exact hne (Finset.prod_eq_zero (List.mem_toFinset.2 he) (by simp [hq0]))
  obtain ⟨w, hw⟩ := exists_support_walk_of_forall_pos q p.1 hpos
  exact absurd (hk w) (by omega)

/-- If every support-graph walk from `x` to `y` has length at least `k`, only simple paths
of length at least `k` contribute to the path-sum bound on `τ(x, y)`. -/
theorem tau_le_tsum_paths_ge [Countable V] (q : Sym2 V → unitInterval) {x y : V} {k : ℕ}
    (hk : ∀ p : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Walk x y, k ≤ p.length) :
    tau q x y ≤ ∑' p : (⊤ : SimpleGraph V).Path x y,
      (if k ≤ p.1.support.tail.length then
        walkWeight (offDiagonal (fun v w => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)))
          x p.1.support.tail.get else 0) := by
  refine (tau_le_tsum_paths q x y).trans (ENNReal.tsum_le_tsum fun p => ?_)
  have hlen : p.1.support.tail.length = p.1.length := by simp
  split_ifs with h
  · exact (path_prod_eq_weight q p).le
  · rw [hlen] at h
    exact (path_prod_eq_zero_of_length_lt q hk p (not_le.1 h)).le

/-- The continuation lists of length at least `k` carry the walk sums of length at least
`k`. -/
theorem tsum_list_ge_eq (a : V → V → ℝ≥0∞) (k : ℕ) (x : V) :
    ∑' l : List V, (if k ≤ l.length then walkWeight a x l.get else 0) =
      ∑' n, (if k ≤ n then walkSum a n x else 0) := by
  set H : (Σ n, Fin n → V) → ℝ≥0∞ := fun t => if k ≤ t.1 then walkWeight a x t.2 else 0
  calc ∑' l : List V, (if k ≤ l.length then walkWeight a x l.get else 0)
      = ∑' l : List V, H (List.equivSigmaTuple l) := rfl
    _ = ∑' t, H t := List.equivSigmaTuple.tsum_eq H
    _ = ∑' n, ∑' f : Fin n → V, H ⟨n, f⟩ := ENNReal.tsum_sigma' _
    _ = ∑' n, (if k ≤ n then walkSum a n x else 0) := by
        refine tsum_congr fun n => ?_
        simp only [H]
        split_ifs
        · rw [walkSum_eq_tsum_walkWeight]
        · simp

/-- **Two-point decay in the support-graph distance.** If every walk from `x` to `y` in
the support graph has length at least `k`, then `τ(x, y) ≤ m ^ k (1 - m)⁻¹`. -/
theorem tau_le_pow_of_walk_length_ge [Countable V] (q : Sym2 V → unitInterval) (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, if w = v then 0 else (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)) ≤ m)
    (hm : m < 1) {x y : V} {k : ℕ}
    (hk : ∀ p : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Walk x y, k ≤ p.length) :
    tau q x y ≤ m ^ k * (1 - m)⁻¹ := by
  set a := offDiagonal (fun v w : V => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞))
  have hinj : Function.Injective fun p : (⊤ : SimpleGraph V).Path x y => p.1.support.tail :=
    fun p r h => by
      have := path_tail_injective x (a₁ := ⟨y, p⟩) (a₂ := ⟨y, r⟩) h
      exact eq_of_heq (Sigma.mk.inj_iff.1 this).2
  calc tau q x y ≤ _ := tau_le_tsum_paths_ge q hk
    _ ≤ ∑' l : List V, (if k ≤ l.length then walkWeight a x l.get else 0) :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj
          (fun l => if k ≤ l.length then walkWeight a x l.get else 0)
    _ = ∑' n, (if k ≤ n then walkSum a n x else 0) := tsum_list_ge_eq a k x
    _ ≤ m ^ k * (1 - m)⁻¹ := tsum_walkSum_ge_le _ m hrow hm k x

/-- **Decay in the support-graph distance.** -/
theorem tau_le_pow_dist [Countable V] (q : Sym2 V → unitInterval) (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, if w = v then 0 else (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)) ≤ m)
    (hm : m < 1) (x y : V) :
    tau q x y ≤ m ^ (SimpleGraph.fromEdgeSet {e | 0 < q e}).dist x y * (1 - m)⁻¹ :=
  tau_le_pow_of_walk_length_ge q m hrow hm fun p => SimpleGraph.dist_le p

/-- **Vertices not joined in the support graph are never connected.** -/
theorem tau_eq_zero_of_not_reachable [Countable V] (q : Sym2 V → unitInterval) {x y : V}
    (h : ¬ (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable x y) : tau q x y = 0 := by
  refine le_antisymm ((tau_le_tsum_paths q x y).trans (le_of_eq ?_)) zero_le
  refine ENNReal.tsum_eq_zero.2 fun p => ?_
  exact path_prod_eq_zero_of_length_lt q (k := p.1.length + 1)
    (fun w => absurd ⟨w⟩ h) p (Nat.lt_succ_self _)

/-- **Tail of the susceptibility.** The vertices that the support graph keeps at walk
distance at least `k` from `x` carry total connection probability at most
`m ^ k (1 - m)⁻¹`. -/
theorem tsum_tau_walk_length_ge_le [Countable V] (q : Sym2 V → unitInterval) (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, if w = v then 0 else (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)) ≤ m)
    (hm : m < 1) (x : V) (k : ℕ) :
    ∑' y, (if ∀ p : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Walk x y, k ≤ p.length
      then tau q x y else 0) ≤ m ^ k * (1 - m)⁻¹ := by
  set a := offDiagonal (fun v w : V => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞))
  set F : List V → ℝ≥0∞ := fun l => if k ≤ l.length then walkWeight a x l.get else 0
  calc ∑' y, (if ∀ p : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Walk x y, k ≤ p.length
        then tau q x y else 0)
      ≤ ∑' y, ∑' p : (⊤ : SimpleGraph V).Path x y, F p.1.support.tail :=
        ENNReal.tsum_le_tsum fun y => by
          split_ifs with hk
          · exact tau_le_tsum_paths_ge q hk
          · exact zero_le
    _ = ∑' p : Σ y, (⊤ : SimpleGraph V).Path x y, F p.2.1.support.tail :=
        (ENNReal.tsum_sigma' (fun p : Σ y, (⊤ : SimpleGraph V).Path x y =>
          F p.2.1.support.tail)).symm
    _ ≤ ∑' l : List V, F l := ENNReal.tsum_comp_le_tsum_of_injective (path_tail_injective x) F
    _ = ∑' n, (if k ≤ n then walkSum a n x else 0) := tsum_list_ge_eq a k x
    _ ≤ m ^ k * (1 - m)⁻¹ := tsum_walkSum_ge_le _ m hrow hm k x

/-! ### Non-vacuity

On `Bool` with every pair open with probability `1/4`, the off-diagonal row sum is `1/4`,
so `m = 1/2` is admissible; the two vertices are at support distance `1`. With `q = 0` the
two vertices are not joined in the support graph and are never connected. -/

/-- The off-diagonal row sum on `Bool` at `q ≡ 1/4` is at most `1/2`. -/
private theorem rowSum_quarter_le (v : Bool) :
    (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (⟨1 / 4, by norm_num, by norm_num⟩ : unitInterval) : ℝ≥0∞)) ≤
      1 / 2 := by
  rw [tsum_fintype, Fintype.sum_bool]
  have : ((unitInterval.toNNReal (⟨1 / 4, by norm_num, by norm_num⟩ : unitInterval) :
      ℝ≥0∞)) ≤ 1 / 2 := by
    rw [show (unitInterval.toNNReal (⟨1 / 4, by norm_num, by norm_num⟩ : unitInterval)) =
      (1 / 4 : ℝ≥0) from NNReal.eq (show ((1 : ℝ) / 4) = ((1 / 4 : ℝ≥0) : ℝ) by
        push_cast; ring)]
    rw [ENNReal.coe_div (by norm_num)]
    simp only [ENNReal.coe_one, ENNReal.coe_ofNat]
    exact ENNReal.div_le_div_left (by norm_num) 1
  cases v <;> simpa using this

example : tau (fun _ : Sym2 Bool => (⟨1 / 4, by norm_num, by norm_num⟩ : unitInterval))
    false true ≤ (1 / 2) ^ 1 * (1 - 1 / 2)⁻¹ := by
  refine tau_le_pow_of_walk_length_ge _ (1 / 2) (fun v => ?_)
    (by norm_num) fun p => ?_
  · convert rowSum_quarter_le v
  · cases p with
    | cons _ p => simp

example : tau (fun _ : Sym2 Bool => (0 : unitInterval)) false true = 0 := by
  refine tau_eq_zero_of_not_reachable _ fun ⟨w⟩ => ?_
  cases w with
  | cons hadj _ =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    exact lt_irrefl (0 : unitInterval) hadj.1

end PercLib.Percolation.Bond
