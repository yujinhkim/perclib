/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for P-7 (issue 41), written on 2026-11-14, from pinned mathlib's finite sums
and simple-graph degrees and the P-5 theorems. No upstream code is copied.
-/
module

public import PercLib.Percolation.Bond.RowSum
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Finite graphs and complete graphs

* `chi_le_of_degree_le`: on a finite vertex type, a profile that is at most `p` on the
  edges of a simple graph `G` and zero on the other off-diagonal pairs satisfies
  `chi ≤ (1 - Δ p)⁻¹` when every degree is at most `Δ` and `Δ p < 1`.
* `chi_completeGraph_le`: on `Fin n`, a profile equal to `p` on every pair of distinct
  vertices has off-diagonal row exactly `(n - 1) p`, so `chi ≤ (1 - (n - 1) p)⁻¹` when
  `(n - 1) p < 1`. The count is `n - 1`, not `n`.

The diagonal of the profile is arbitrary in both. On a finite vertex type every cluster
is finite at every parameter, for the deterministic reason that there are finitely many
vertices; the row criterion is sufficient for the susceptibility bound, not a
characterisation of finite clusters.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open Classical
open PercLib.Percolation.Bond

namespace PercLib.Models

/-- **Finite graph.** A profile that is at most `p` on the edges of a simple graph of
maximum degree at most `Δ`, and zero on its other off-diagonal pairs, has susceptibility
at most `(1 - Δ p)⁻¹` when `Δ p < 1`. -/
theorem chi_le_of_degree_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (q : Sym2 V → unitInterval) (p : unitInterval)
    (hon : ∀ v w, G.Adj v w → q s(v,w) ≤ p)
    (hoff : ∀ v w, v ≠ w → ¬ G.Adj v w → q s(v,w) = 0)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (hp : (Δ : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) < 1) (x : V) :
    chi q x ≤ (1 - (Δ : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞))⁻¹ := by
  refine chi_le_inv_one_sub_of_rowSum q _ (fun v => ?_) hp x
  rw [tsum_fintype]
  calc _ ≤ ∑ w, if w ∈ G.neighborFinset v then (unitInterval.toNNReal p : ℝ≥0∞) else 0 := by
        refine Finset.sum_le_sum fun w _ => ?_
        by_cases hw : w = v
        · rw [ite_eq_left hw]
          exact zero_le
        · rw [ite_eq_right hw]
          by_cases ha : G.Adj v w
          · rw [ite_eq_left (by simp [ha])]
            exact ENNReal.coe_le_coe.2 (hon v w ha)
          · rw [ite_eq_right (by simp [ha]), hoff v w (Ne.symm hw) ha]
            simp
    _ = (G.degree v : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          G.card_neighborFinset_eq_degree, nsmul_eq_mul]
    _ ≤ (Δ : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) := by
        gcongr
        exact_mod_cast hdeg v

/-- **Complete graph.** On `Fin n`, a profile equal to `p` on every pair of distinct
vertices has off-diagonal row `(n - 1) p` at every vertex. The diagonal is arbitrary. -/
theorem chi_completeGraph_le (n : ℕ) (q : Sym2 (Fin n) → unitInterval) (p : unitInterval)
    (hq : ∀ v w, v ≠ w → q s(v,w) = p)
    (hp : ((n - 1 : ℕ) : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) < 1) (x : Fin n) :
    chi q x ≤ (1 - ((n - 1 : ℕ) : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞))⁻¹ := by
  refine chi_le_inv_one_sub_of_rowSum q _ (fun v => le_of_eq ?_) hp x
  rw [tsum_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ v),
    Finset.sum_congr rfl (g := fun _ => (unitInterval.toNNReal p : ℝ≥0∞))]
  · rw [ite_eq_left rfl, zero_add, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro w hw
    rw [ite_eq_right (Finset.ne_of_mem_erase hw), hq v w (Ne.symm (Finset.ne_of_mem_erase hw))]

/-- **Complete graph, `n = 1`.** With one vertex there is no off-diagonal pair, and the
susceptibility is one whatever the diagonal value. -/
theorem chi_fin_one (q : Sym2 (Fin 1) → unitInterval) (x : Fin 1) : chi q x = 1 :=
  chi_eq_one_of_offDiagonal_zero q (fun v w h => absurd (Subsingleton.elim w v) h) x

end PercLib.Models

/-! ### Non-vacuity -/
section Witnesses

open PercLib.Models

/-- The complete graph on three vertices at `p = 1/4`, with diagonal value one:
`(n - 1) p = 1/2 < 1` and the susceptibility is at most two. -/
example (x : Fin 3) :
    chi (fun e : Sym2 (Fin 3) => if e.IsDiag then 1 else (⟨1 / 4, by norm_num⟩ : unitInterval))
      x ≤ (1 - ((3 - 1 : ℕ) : ℝ≥0∞) *
        (unitInterval.toNNReal (⟨1 / 4, by norm_num⟩ : unitInterval) : ℝ≥0∞))⁻¹ := by
  refine chi_completeGraph_le 3 _ _ (fun v w h => ?_) ?_ x
  · simp [Sym2.mk_isDiag_iff, h]
  · rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]
    change ((3 - 1 : ℕ) : ℝ≥0) * (1 / 4 : ℝ≥0) < 1
    norm_num

/-- The single-vertex complete graph with open loop has susceptibility one. -/
example : chi (fun _ : Sym2 (Fin 1) => (1 : unitInterval)) 0 = 1 := chi_fin_one _ 0

/-- A nonempty finite host: the complete graph on `Bool` at `p = 1/2`, with maximum
degree one. -/
example (x : Bool) :
    chi (fun e : Sym2 Bool => if e.IsDiag then 0 else (⟨1 / 2, by norm_num⟩ : unitInterval))
      x ≤ (1 - ((1 : ℕ) : ℝ≥0∞) *
        (unitInterval.toNNReal (⟨1 / 2, by norm_num⟩ : unitInterval) : ℝ≥0∞))⁻¹ := by
  refine chi_le_of_degree_le (⊤ : SimpleGraph Bool) _ _ (fun v w h => ?_)
    (fun v w h hn => absurd ((SimpleGraph.top_adj v w).2 h) hn)
    1 (fun v => by
      have h := (⊤ : SimpleGraph Bool).degree_lt_card_verts v
      rw [Fintype.card_bool] at h
      omega) ?_ x
  · simp [Sym2.mk_isDiag_iff, ((SimpleGraph.top_adj v w).1 h)]
  · rw [← ENNReal.coe_natCast, ← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]
    change ((1 : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) < 1
    norm_num

end Witnesses
