/-
New indicator expansions on the canonical bond interface, using pinned mathlib's
ENNReal sums and Tonelli theorem (56a005855ea17e0b0958f73ec801ae140b0a1679).
No upstream moment bound or percolation theorem is assumed.
-/
module

public import PercLib.Percolation.Bond.Susceptibility

/-! # Cluster second moments and joint connections

Finite mixed moments are double sums of joint connection probabilities. The full
countable identities take values in ENNReal and allow infinity. The finite-domain
volume here is the intersection of the ambient cluster with the specified domain.
No tree-graph or BK inequality is asserted.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Cluster volume in a finite domain is the sum of its connection indicators. -/
theorem encard_cluster_inter_finset_eq_sum (ω : Config V) (v : V) (F : Finset V) :
    ((cluster ω v ∩ (F : Set V)).encard : ℝ≥0∞) =
      ∑ x ∈ F, (conn v x).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [← ENNReal.tsum_set_one, tsum_subtype (cluster ω v ∩ (F : Set V)) (fun _ => (1 : ℝ≥0∞))]
  rw [tsum_eq_sum (s := F) (fun x hx => by simp [hx])]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : (openGraph ω).Reachable v x <;> simp [h, hx, cluster, conn, Set.indicator]

private theorem indicator_conn_mul (u v x y : V) (ω : Config V) :
    (conn u x).indicator (fun _ => (1 : ℝ≥0∞)) ω *
      (conn v y).indicator (fun _ => (1 : ℝ≥0∞)) ω =
    (conn u x ∩ conn v y).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases hx : ω ∈ conn u x <;> by_cases hy : ω ∈ conn v y <;>
    simp [Set.indicator, hx, hy]

/-- Pointwise finite-domain mixed-volume expansion, requiring no countability. -/
theorem encard_cluster_inter_mul_eq_sum (ω : Config V) (u v : V) (F D : Finset V) :
    ((cluster ω u ∩ (F : Set V)).encard : ℝ≥0∞) *
      ((cluster ω v ∩ (D : Set V)).encard : ℝ≥0∞) =
    ∑ x ∈ F, ∑ y ∈ D, (conn u x ∩ conn v y).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [encard_cluster_inter_finset_eq_sum, encard_cluster_inter_finset_eq_sum,
    Finset.sum_mul]
  simp_rw [Finset.mul_sum, indicator_conn_mul]

/-- Exact finite-domain mixed moment, with possibly different roots and domains. -/
theorem lintegral_cluster_inter_mul [Countable V] (q : Sym2 V → unitInterval)
    (u v : V) (F D : Finset V) :
    (∫⁻ ω, ((cluster ω u ∩ (F : Set V)).encard : ℝ≥0∞) *
      ((cluster ω v ∩ (D : Set V)).encard : ℝ≥0∞) ∂law q) =
    ∑ x ∈ F, ∑ y ∈ D, law q (conn u x ∩ conn v y) := by
  have hm (x y : V) : Measurable
      ((conn u x ∩ conn v y).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator ((measurableSet_conn u x).inter (measurableSet_conn v y))
  simp_rw [encard_cluster_inter_mul_eq_sum]
  rw [lintegral_finsetSum F (by intros; fun_prop)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [lintegral_finsetSum D (fun y _ => hm x y)]
  apply Finset.sum_congr rfl
  intro y hy
  exact lintegral_indicator_one ((measurableSet_conn u x).inter (measurableSet_conn v y))

/-- The finite-domain second moment is the sum of joint connections from the root. -/
theorem lintegral_cluster_inter_sq [Countable V] (q : Sym2 V → unitInterval)
    (v : V) (F : Finset V) :
    (∫⁻ ω, ((cluster ω v ∩ (F : Set V)).encard : ℝ≥0∞) ^ 2 ∂law q) =
      ∑ x ∈ F, ∑ y ∈ F, law q (conn v x ∩ conn v y) := by
  simpa only [pow_two] using lintegral_cluster_inter_mul q v v F F

/-- The full mixed volume expands as a countable double sum, allowing infinity. -/
theorem encard_cluster_mul_eq_tsum (ω : Config V) (u v : V) :
    ((cluster ω u).encard : ℝ≥0∞) * ((cluster ω v).encard : ℝ≥0∞) =
      ∑' x, ∑' y, (conn u x ∩ conn v y).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [encard_cluster_eq_tsum, encard_cluster_eq_tsum]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, indicator_conn_mul]

/-- Tonelli gives the full mixed-root moment without any finiteness assumption. -/
theorem lintegral_cluster_mul [Countable V] (q : Sym2 V → unitInterval) (u v : V) :
    (∫⁻ ω, ((cluster ω u).encard : ℝ≥0∞) * ((cluster ω v).encard : ℝ≥0∞) ∂law q) =
      ∑' x, ∑' y, law q (conn u x ∩ conn v y) := by
  have hm (x y : V) : Measurable
      ((conn u x ∩ conn v y).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator ((measurableSet_conn u x).inter (measurableSet_conn v y))
  simp_rw [encard_cluster_mul_eq_tsum]
  rw [lintegral_tsum (by intro x; exact (Measurable.tsum (hm x)).aemeasurable)]
  congr 1
  funext x
  rw [lintegral_tsum (fun y => (hm x y).aemeasurable)]
  congr 1
  funext y
  exact lintegral_indicator_one ((measurableSet_conn u x).inter (measurableSet_conn v y))

/-- Full second moment as a double connection sum, including infinite second moment. -/
theorem lintegral_cluster_sq [Countable V] (q : Sym2 V → unitInterval) (v : V) :
    (∫⁻ ω, ((cluster ω v).encard : ℝ≥0∞) ^ 2 ∂law q) =
      ∑' x, ∑' y, law q (conn v x ∩ conn v y) := by
  simpa only [pow_two] using lintegral_cluster_mul q v v

/-- Exhaustion by any cofinal family of finite domains recovers the full second
moment. No finite second-moment assumption or monotonicity of the indexing is needed. -/
theorem lintegral_cluster_sq_eq_iSup [Countable V] {ι : Type*}
    (q : Sym2 V → unitInterval) (v : V) (F : ι → Finset V)
    (hF : ∀ s : Finset V, ∃ i, s ⊆ F i) :
    (∫⁻ ω, ((cluster ω v).encard : ℝ≥0∞) ^ 2 ∂law q) =
      ⨆ i, ∫⁻ ω, ((cluster ω v ∩ (F i : Set V)).encard : ℝ≥0∞) ^ 2 ∂law q := by
  have hprod : ∀ t : Finset (V × V), ∃ i, t ⊆ (F i).product (F i) := by
    intro t
    obtain ⟨i, hi⟩ := hF (t.image Prod.fst ∪ t.image Prod.snd)
    refine ⟨i, ?_⟩
    intro p hp
    exact Finset.mem_product.mpr
      ⟨hi (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)),
       hi (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))⟩
  simp_rw [lintegral_cluster_sq, lintegral_cluster_inter_sq]
  rw [← ENNReal.tsum_prod, ENNReal.tsum_eq_iSup_sum' _ hprod]
  congr 1
  funext i
  exact Finset.sum_product' (F i) (F i) (fun x y => law q (conn v x ∩ conn v y))

-- A singleton cluster contributes one, even when the loop has an arbitrary marginal.
example (q : Sym2 Unit → unitInterval) :
    (∫⁻ ω, ((cluster ω ()).encard : ℝ≥0∞) ^ 2 ∂law q) = 1 := by
  rw [lintegral_cluster_sq]
  simp [conn_self]

-- Empty domains contribute zero rather than a base-vertex term.
example [Countable V] (q : Sym2 V → unitInterval) (u v : V) (D : Finset V) :
    (∫⁻ ω, ((cluster ω u ∩ (∅ : Set V)).encard : ℝ≥0∞) *
      ((cluster ω v ∩ (D : Set V)).encard : ℝ≥0∞) ∂law q) = 0 := by
  simp

-- Infinite second moments are retained by the ENNReal formulation.
example : (∫⁻ ω, ((cluster ω (0 : ℕ)).encard : ℝ≥0∞) ^ 2
    ∂law (fun _ : Sym2 ℕ => 1)) = ∞ := by
  have hc : cluster (Set.univ : Config ℕ) 0 = Set.univ := by
    ext y
    simp [cluster, openGraph, SimpleGraph.fromEdgeSet_univ]
  simp [law, PercLib.Probability.prodBernoulli_const, hc]

-- The usual increasing finite exhaustion is a concrete cofinal witness.
example (q : Sym2 ℕ → unitInterval) (v : ℕ) :
    (∫⁻ ω, ((cluster ω v).encard : ℝ≥0∞) ^ 2 ∂law q) =
      ⨆ n, ∫⁻ ω, ((cluster ω v ∩ (Finset.range n : Set ℕ)).encard : ℝ≥0∞) ^ 2 ∂law q :=
  lintegral_cluster_sq_eq_iSup q v Finset.range Finset.exists_nat_subset_range

end PercLib.Percolation.Bond
