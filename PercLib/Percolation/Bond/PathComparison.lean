/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs comparing cluster tails, percolation probabilities and susceptibilities at
two roots joined by a path (wiki infinite-cluster-zero-one, tag C3OO). No upstream
proof is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.PathLowerBounds
public import PercLib.Percolation.Bond.RootIndependence
public import PercLib.Percolation.Bond.VolumeTails

/-! # Comparison of two roots along a path

For a walk `γ` from `x` to `y` in the complete graph, put
`ρ_γ = ∏_{e ∈ E_γ} q e`. The event that `γ` is open and any increasing event at `y` are
positively correlated (Harris), and on their intersection the cluster of `x` is the
cluster of `y`. Hence
* `ρ_γ P(n ≤ |K_y|) ≤ P(n ≤ |K_x|)` for every `n`,
* `ρ_γ θ(y) ≤ θ(x)`,
* `ρ_γ χ(y) ≤ χ(x)` in `ℝ≥0∞`,
and on each component of the support graph `{e | 0 < q e}` positivity of `θ` and
finiteness of `χ` do not depend on the root. The values themselves need not agree.
The bounds are proved first with the two-point function `τ(y,x)` in place of `ρ_γ`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Volume tail events are increasing. -/
theorem isUpperSet_le_encard_cluster (x : V) (n : ℕ∞) :
    IsUpperSet {ω : Config V | n ≤ (cluster ω x).encard} :=
  fun _ _ h hω => hω.trans (encard_le_encard (cluster_mono h x))

/-- **Volume tails along a connection.** `τ(y,x) P(n ≤ |K_y|) ≤ P(n ≤ |K_x|)`. -/
theorem tau_mul_law_le_encard_le [Countable V] (q : Sym2 V → unitInterval) (x y : V)
    (n : ℕ∞) :
    tau q y x * law q {ω | n ≤ (cluster ω y).encard} ≤
      law q {ω | n ≤ (cluster ω x).encard} := by
  refine (prodBernoulli_harris q (isUpperSet_conn y x) (isUpperSet_le_encard_cluster y n)
    (measurableSet_conn y x) (measurableSet_le_encard_cluster y n)).trans (measure_mono ?_)
  rintro ω ⟨hyx, hn⟩
  change n ≤ (cluster ω x).encard
  rwa [← cluster_eq_of_mem_conn hyx]

/-- **Susceptibility along a connection.** `τ(y,x) χ(y) ≤ χ(x)`. -/
theorem tau_mul_chi_le [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    tau q y x * chi q y ≤ chi q x := by
  rw [chi_eq_tsum_law_le_encard, chi_eq_tsum_law_le_encard, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun n => tau_mul_law_le_encard_le q x y _

/-- The probability that a walk of the complete graph is open is at most the two-point
function in either direction. -/
theorem prod_edges_le_tau_symm [DecidableEq V] (q : Sym2 V → unitInterval) {x y : V}
    (γ : (⊤ : SimpleGraph V).Walk x y) :
    (∏ e ∈ γ.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) ≤ tau q y x := by
  have h := prod_le_tau_of_walk q γ.reverse
  rwa [SimpleGraph.Walk.edges_reverse, List.toFinset_reverse] at h

/-- **Item 1: volume tails along a path.** For a walk `γ` of the complete graph from `x`
to `y` and every `n`, `ρ_γ P(n ≤ |K_y|) ≤ P(n ≤ |K_x|)`. -/
theorem prod_edges_mul_law_le_encard_le [Countable V] [DecidableEq V]
    (q : Sym2 V → unitInterval) {x y : V} (γ : (⊤ : SimpleGraph V).Walk x y) (n : ℕ) :
    (∏ e ∈ γ.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) *
        law q {ω | (n : ℕ∞) ≤ (cluster ω y).encard} ≤
      law q {ω | (n : ℕ∞) ≤ (cluster ω x).encard} :=
  (mul_le_mul' (prod_edges_le_tau_symm q γ) le_rfl).trans (tau_mul_law_le_encard_le q x y n)

/-- **Item 2: percolation along a path.** `ρ_γ θ(y) ≤ θ(x)`. -/
theorem prod_edges_mul_law_cluster_infinite_le [Countable V] [DecidableEq V]
    (q : Sym2 V → unitInterval) {x y : V} (γ : (⊤ : SimpleGraph V).Walk x y) :
    (∏ e ∈ γ.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) *
        law q {ω | (cluster ω y).Infinite} ≤ law q {ω | (cluster ω x).Infinite} :=
  (mul_le_mul' (prod_edges_le_tau_symm q γ) le_rfl).trans
    (tau_mul_law_cluster_infinite_le q y x)

/-- **Item 3: susceptibility along a path.** `ρ_γ χ(y) ≤ χ(x)`, infinite values allowed. -/
theorem prod_edges_mul_chi_le [Countable V] [DecidableEq V] (q : Sym2 V → unitInterval)
    {x y : V} (γ : (⊤ : SimpleGraph V).Walk x y) :
    (∏ e ∈ γ.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) * chi q y ≤ chi q x :=
  (mul_le_mul' (prod_edges_le_tau_symm q γ) le_rfl).trans (tau_mul_chi_le q x y)

/-- **Item 4: positivity of `θ` is constant on components of the support graph.** -/
theorem law_cluster_infinite_pos_iff_of_reachable [Countable V] (q : Sym2 V → unitInterval)
    {x y : V} (h : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable x y) :
    0 < law q {ω | (cluster ω x).Infinite} ↔ 0 < law q {ω | (cluster ω y).Infinite} := by
  have key : ∀ a b : V, (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable a b →
      0 < law q {ω | (cluster ω a).Infinite} → 0 < law q {ω | (cluster ω b).Infinite} :=
    fun a b hab ha => lt_of_lt_of_le (ENNReal.mul_pos (tau_pos_of_reachable q hab).ne' ha.ne')
      (tau_mul_law_cluster_infinite_le q a b)
  exact ⟨key x y h, key y x h.symm⟩

/-- **Item 4: finiteness of `χ` is constant on components of the support graph.** -/
theorem chi_ne_top_iff_of_reachable [Countable V] (q : Sym2 V → unitInterval) {x y : V}
    (h : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable x y) :
    chi q x ≠ ∞ ↔ chi q y ≠ ∞ := by
  have key : ∀ a b : V, (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable a b →
      chi q a ≠ ∞ → chi q b ≠ ∞ := by
    intro a b hab ha hb
    have hle := tau_mul_chi_le q a b
    rw [hb, ENNReal.mul_top (tau_pos_of_reachable q hab.symm).ne', top_le_iff] at hle
    exact ha hle
  exact ⟨key x y h, key y x h.symm⟩

-- Non-vacuity: two vertices joined by one pair of probability `1/2`, so `ρ_γ = 1/2`.
example : (2⁻¹ : ℝ≥0∞) *
      law (fun _ : Sym2 Bool => (⟨1/2, by norm_num, by norm_num⟩ : unitInterval))
        {ω | ((2 : ℕ) : ℕ∞) ≤ (cluster ω true).encard} ≤
    law (fun _ : Sym2 Bool => (⟨1/2, by norm_num, by norm_num⟩ : unitInterval))
      {ω | ((2 : ℕ) : ℕ∞) ≤ (cluster ω false).encard} := by
  have hadj : (⊤ : SimpleGraph Bool).Adj false true := by simp
  have h := prod_edges_mul_law_le_encard_le
    (fun _ : Sym2 Bool => (⟨1/2, by norm_num, by norm_num⟩ : unitInterval))
    (SimpleGraph.Walk.cons hadj .nil) 2
  have hq : unitInterval.toNNReal (⟨1/2, by norm_num, by norm_num⟩ : unitInterval) = 2⁻¹ :=
    NNReal.eq (by norm_num [unitInterval.toNNReal]; rfl)
  have hρ : (∏ _e ∈ (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).edges.toFinset,
      (unitInterval.toNNReal (⟨1/2, by norm_num, by norm_num⟩ : unitInterval) : ℝ≥0∞)) =
      2⁻¹ := by
    rw [Finset.prod_const, hq]
    simp [ENNReal.coe_inv two_ne_zero]
  rw [hρ] at h
  exact h

end PercLib.Percolation.Bond
