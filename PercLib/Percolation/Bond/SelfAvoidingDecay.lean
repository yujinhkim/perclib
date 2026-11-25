/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 225, Q-48, item 4 for the two-point function). No upstream proof
is copied.
-/
module

public import PercLib.Percolation.Bond.SelfAvoiding

/-!
# Self-avoiding decay of the two-point function on bounded-degree graphs

On a graph `G` of maximal degree `Δ`, with a profile supported on `G` off the diagonal and at
most `p` on its edges, an open path from `x ≠ y` to `y` is a `G`-path of length at least
`G.dist x y`, and there are at most `Δ (Δ - 1)^n` `G`-paths of length `n + 1` from `x`, so

`τ(x, y) ≤ ∑_{n + 1 ≥ dist(x, y)} Δ (Δ - 1)^n p^{n+1}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **Self-avoiding decay of `τ`.** -/
theorem tau_le_of_degree_le_dist [Countable V] (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    {x y : V} (hxy : x ≠ y) :
    tau q x y ≤ ∑' n : ℕ, if G.dist x y ≤ n + 1 then
      (Δ : ℝ≥0∞) * ((Δ : ℝ≥0∞) - 1) ^ n * (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1) else 0 := by
  classical
  set E : ℕ → Set (Config V) := fun n =>
    if G.dist x y ≤ n + 1 then {ω | ∃ y', ∃ r : G.Path x y', r.1.length = n + 1 ∧
      (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} else ∅ with hE
  have hsub : ∀ᵐ ω ∂law q, ω ∈ conn x y → ω ∈ ⋃ n, E n := by
    filter_upwards [ae_openGraph_le_of_zero_off_diagonal G q hoff] with ω hω hconn
    obtain ⟨w, hw⟩ := (hconn : (openGraph ω).Reachable x y).exists_isPath
    have hlen : w.length ≠ 0 := fun h => hxy (SimpleGraph.Walk.eq_of_length_eq_zero h)
    obtain ⟨n, hn⟩ : ∃ n, w.length = n + 1 := ⟨w.length - 1, by omega⟩
    have hedG : ∀ e ∈ w.edges, e ∈ G.edgeSet := fun e he =>
      SimpleGraph.edgeSet_mono hω (w.edges_subset_edgeSet he)
    set wG := w.transfer G hedG
    have hpath : wG.IsPath := hw.transfer hedG
    refine mem_iUnion.2 ⟨n, ?_⟩
    have hdist : G.dist x y ≤ n + 1 := by
      have := SimpleGraph.dist_le wG
      rwa [SimpleGraph.Walk.length_transfer, hn] at this
    simp only [hE, hdist, ite_true, mem_ofPred_eq]
    refine ⟨y, ⟨wG, hpath⟩, by rw [SimpleGraph.Walk.length_transfer, hn], fun e he => ?_⟩
    simp only [wG, SimpleGraph.Walk.edges_transfer, List.coe_toFinset, mem_ofPred_eq] at he
    have h1 := w.edges_subset_edgeSet he
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1
    exact h1.1
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

/-! ### Non-vacuity -/

/-- The complete graph on `Fin 3` (`Δ = 2`) with any constant profile. -/
example (p : unitInterval) :
    tau (fun _ : Sym2 (Fin 3) => p) 0 1 ≤ ∑' n : ℕ,
      if (⊤ : SimpleGraph (Fin 3)).dist 0 1 ≤ n + 1 then
        ((2 : ℕ) : ℝ≥0∞) * (((2 : ℕ) : ℝ≥0∞) - 1) ^ n *
          (unitInterval.toNNReal p : ℝ≥0∞) ^ (n + 1) else 0 :=
  tau_le_of_degree_le_dist (⊤ : SimpleGraph (Fin 3)) (fun v => Nat.lt_succ_iff.1 (by simp)) _ p
    (fun e hd he => absurd (SimpleGraph.edgeSet_top ▸ hd :
      e ∈ (⊤ : SimpleGraph (Fin 3)).edgeSet) he)
    (fun _ _ => le_rfl) (by decide)

end PercLib.Percolation.Bond

end
