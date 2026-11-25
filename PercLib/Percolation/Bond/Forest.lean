/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs using pinned mathlib's acyclic graphs and walks, and PercLib's canonical
Bernoulli cylinders. No upstream proof copied. Diagonal probabilities are unrestricted.
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.Cylinder
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Nat.Dist

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal Classical

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Almost surely every open coordinate has positive prescribed probability,
including diagonal coordinates. -/
theorem ae_config_subset_positive [Countable V] (q : Sym2 V → unitInterval) :
    ∀ᵐ ω ∂law q, ω ⊆ {e | 0 < q e} := by
  have he (e : Sym2 V) : ∀ᵐ ω ∂law q, e ∈ ω → 0 < q e := by
    by_cases h : 0 < q e
    · exact Filter.Eventually.of_forall (fun _ _ => h)
    · have hz : q e = 0 := le_antisymm (not_lt.mp h) zero_le
      rw [ae_iff]
      simpa [h, law, hz] using prodBernoulli_setOf_mem q e
  filter_upwards [ae_all_iff.mpr he] with ω hω
  exact fun e he => hω e he

/-- The random open graph is almost surely contained in the positive-probability support. -/
theorem ae_openGraph_le_support [Countable V] (q : Sym2 V → unitInterval) :
    ∀ᵐ ω ∂law q, openGraph ω ≤ SimpleGraph.fromEdgeSet {e | 0 < q e} := by
  filter_upwards [ae_config_subset_positive q] with ω hω
  exact SimpleGraph.fromEdgeSet_mono hω

/-- A walk whose edges are all open certifies a connection. -/
theorem mem_conn_of_walk_edges {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    {ω : Config V} (hp : ∀ e ∈ p.edges, e ∈ ω) : ω ∈ conn x y := by
  refine ⟨p.transfer (openGraph ω) ?_⟩
  intro e he
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨hp e he, G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he)⟩

/-- Inside an acyclic host, connection is equivalent to opening every edge of its
unique simple path. The nil path is included. -/
theorem mem_conn_iff_path_edges_of_le {G : SimpleGraph V} (hG : G.IsAcyclic)
    {x y : V} (p : G.Path x y) {ω : Config V} (hω : openGraph ω ≤ G) :
    ω ∈ conn x y ↔ (p.1.edges.toFinset : Set (Sym2 V)) ⊆ ω := by
  constructor
  · intro hc
    obtain ⟨r, hr⟩ := hc.exists_isPath
    have heq : (⟨r.mapLe hω, hr.mapLe hω⟩ : G.Path x y) = p :=
      (hG.subsingleton_path x y).elim _ _
    have hedges := congrArg (fun a : G.Path x y => a.1.edges) heq
    intro e he
    have her : e ∈ r.edges := by simpa [← hedges] using he
    have hmem := r.edges_subset_edgeSet her
    exact (show e ∈ ω \ Sym2.diagSet by
      simpa [openGraph, SimpleGraph.edgeSet_fromEdgeSet] using hmem).1
  · intro hp
    exact mem_conn_of_walk_edges p.1 (by intro e he; exact hp (by simpa using he))

/-- Exact path probability for any almost-sure acyclic host. -/
theorem tau_eq_prod_of_ae_le_acyclic [Countable V] (q : Sym2 V → unitInterval)
    {G : SimpleGraph V} (hG : G.IsAcyclic)
    (hhost : ∀ᵐ ω ∂law q, openGraph ω ≤ G) {x y : V} (p : G.Path x y) :
    tau q x y = ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) := by
  change law q (conn x y) = _
  rw [← prodBernoulli_subset q p.1.edges.toFinset]
  apply measure_congr
  filter_upwards [hhost] with ω hω
  exact propext (mem_conn_iff_path_edges_of_le hG p hω)

/-- Exact two-point function when the positive-probability support is a forest. -/
theorem tau_eq_prod_of_isAcyclic [Countable V] (q : Sym2 V → unitInterval)
    (hG : (SimpleGraph.fromEdgeSet {e | 0 < q e}).IsAcyclic) {x y : V}
    (p : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Path x y) :
    tau q x y = ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) :=
  tau_eq_prod_of_ae_le_acyclic q hG (ae_openGraph_le_support q) p

/-- Vertices disconnected in any almost-sure host have zero connection probability. -/
theorem tau_eq_zero_of_ae_le (q : Sym2 V → unitInterval) {G : SimpleGraph V}
    (hhost : ∀ᵐ ω ∂law q, openGraph ω ≤ G) {x y : V}
    (h : ¬ G.Reachable x y) : tau q x y = 0 := by
  change law q (conn x y) = 0
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hhost] with ω hω hc
  exact h (hc.mono hω)

/-- Susceptibility is the exact sum of support-path weights in a forest.
There is at most one path to each vertex, and the root contributes its empty path. -/
theorem chi_eq_tsum_paths_of_isAcyclic [Countable V] (q : Sym2 V → unitInterval)
    (hG : (SimpleGraph.fromEdgeSet {e | 0 < q e}).IsAcyclic) (x : V) :
    chi q x = ∑' y, ∑' p : (SimpleGraph.fromEdgeSet {e | 0 < q e}).Path x y,
      ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) := by
  rw [chi_eq_tsum_tau]
  apply tsum_congr
  intro y
  let G := SimpleGraph.fromEdgeSet {e | 0 < q e}
  let : Subsingleton (G.Path x y) := hG.subsingleton_path x y
  by_cases h : G.Reachable x y
  · obtain ⟨p, hp⟩ := h.exists_isPath
    let r : G.Path x y := ⟨p, hp⟩
    rw [tsum_eq_single r]
    · exact tau_eq_prod_of_isAcyclic q hG r
    · intro b hb; exact (hb (Subsingleton.elim _ _)).elim
  · let : IsEmpty (G.Path x y) := ⟨fun p => h ⟨p.1⟩⟩
    rw [tsum_empty]
    exact tau_eq_zero_of_ae_le q (ae_openGraph_le_support q) h

/-- The ray has a simple increasing path of the expected length. -/
theorem exists_hasse_nat_path {m n : ℕ} (h : m ≤ n) :
    ∃ p : (SimpleGraph.hasse ℕ).Path m n, p.1.length = n - m ∧
      ∀ v ∈ p.1.support, v ≤ n := by
  induction n, h using Nat.le_induction with
  | base =>
    exact ⟨⟨.nil, by simp⟩, by simp, by simp⟩
  | succ n h ih =>
    obtain ⟨p, hlen, hsupp⟩ := ih
    have hadj : (SimpleGraph.hasse ℕ).Adj n (n + 1) := by simp
    have hnot : n + 1 ∉ p.1.support := by
      intro hm
      have := hsupp _ hm
      omega
    refine ⟨⟨p.1.concat hadj, p.2.concat hnot hadj⟩, ?_, ?_⟩
    · simp only [SimpleGraph.Walk.length_concat, hlen]
      omega
    · intro v hv
      simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact (hsupp _ hv).trans (Nat.le_succ n)
      · exact le_rfl

/-- A nearest-neighbour profile on ℕ has the ray as an almost-sure host;
no condition is imposed on diagonal coordinates. -/
theorem ae_openGraph_le_hasse_nat (q : Sym2 ℕ → unitInterval)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m,n) = 0) :
    ∀ᵐ ω ∂law q, openGraph ω ≤ SimpleGraph.hasse ℕ := by
  filter_upwards [ae_config_subset_positive q] with ω hω
  intro m n hmn
  obtain ⟨he, hne⟩ := (openGraph_adj_iff ω m n).mp hmn
  have hpos := hω he
  by_contra hn
  have hzero := hz m n hne (by simpa using hn)
  simp [hzero] at hpos

/-- Exact ray connection probability, first in increasing endpoint order. -/
theorem tau_nat_eq_pow_of_le (q : Sym2 ℕ → unitInterval) (t : unitInterval)
    (hedge : ∀ n, q s(n,n+1) = t)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m,n) = 0)
    {m n : ℕ} (hmn : m ≤ n) :
    tau q m n = (unitInterval.toNNReal t : ℝ≥0∞) ^ (n - m) := by
  classical
  obtain ⟨p, hlen, _⟩ := exists_hasse_nat_path hmn
  have hprob : ∀ e ∈ p.1.edges.toFinset, q e = t := by
    intro e he
    induction e using Sym2.ind with | _ a b =>
    have ha := p.1.adj_of_mem_edges (List.mem_toFinset.mp he)
    simp only [SimpleGraph.hasse_adj, Nat.covBy_iff_add_one_eq] at ha
    rcases ha with rfl | rfl
    · exact hedge a
    · rw [Sym2.eq_swap]; exact hedge b
  calc
    tau q m n = ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) := by
      convert tau_eq_prod_of_ae_le_acyclic q (SimpleGraph.isAcyclic_hasse_of_linearOrder ℕ)
        (ae_openGraph_le_hasse_nat q hz) p using 1
      congr 1
      ext e
      simp only [List.mem_toFinset]
    _ = ∏ _e ∈ p.1.edges.toFinset, (unitInterval.toNNReal t : ℝ≥0∞) :=
      Finset.prod_congr rfl (fun e he => congrArg
        (fun u : unitInterval => (unitInterval.toNNReal u : ℝ≥0∞)) (hprob e he))
    _ = _ := by
      rw [Finset.prod_const, List.toFinset_card_of_nodup p.2.isTrail.edges_nodup,
        SimpleGraph.Walk.length_edges, hlen]

/-- Exact ray connection probability for either endpoint order. -/
theorem tau_nat_eq_pow_dist (q : Sym2 ℕ → unitInterval) (t : unitInterval)
    (hedge : ∀ n, q s(n,n+1) = t)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m,n) = 0)
    (m n : ℕ) : tau q m n = (unitInterval.toNNReal t : ℝ≥0∞) ^ Nat.dist m n := by
  rcases le_total m n with h | h
  · simpa [Nat.dist_eq_sub_of_le h] using tau_nat_eq_pow_of_le q t hedge hz h
  · rw [tau_comm]
    simpa [Nat.dist_eq_sub_of_le_right h] using tau_nat_eq_pow_of_le q t hedge hz h

/-- The susceptibility at the endpoint of the ray is the full geometric sum.
This equality includes t=1, when both sides are infinite. -/
theorem chi_nat_zero_eq_geometric (q : Sym2 ℕ → unitInterval) (t : unitInterval)
    (hedge : ∀ n, q s(n,n+1) = t)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m,n) = 0) :
    chi q 0 = (1 - (unitInterval.toNNReal t : ℝ≥0∞))⁻¹ := by
  rw [chi_eq_tsum_tau]
  simp_rw [tau_nat_eq_pow_dist q t hedge hz, Nat.dist_zero_left]
  exact ENNReal.tsum_geometric _

/-- Strictly subunit ray probabilities give finite endpoint susceptibility. -/
theorem chi_nat_zero_lt_top (q : Sym2 ℕ → unitInterval) (t : unitInterval) (ht : t < 1)
    (hedge : ∀ n, q s(n,n+1) = t)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m,n) = 0) :
    chi q 0 < ⊤ := by
  rw [chi_nat_zero_eq_geometric q t hedge hz, ENNReal.inv_lt_top]
  apply tsub_pos_of_lt
  rw [ENNReal.coe_lt_one_iff]
  exact ht

-- At the endpoint t=1, the root term and the infinite tail are both retained.
example (q : Sym2 ℕ → unitInterval) (hedge : ∀ n, q s(n,n+1) = 1)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m,n) = 0) :
    chi q 0 = ⊤ := by
  simpa using chi_nat_zero_eq_geometric q 1 hedge hz

-- The hypotheses are inhabited for every t, with any diagonal profile.
example (t : unitInterval) (d : ℕ → unitInterval) :
    ∃ q : Sym2 ℕ → unitInterval,
      (∀ n, q s(n,n) = d n) ∧
      (∀ m n, tau q m n = (unitInterval.toNNReal t : ℝ≥0∞) ^ Nat.dist m n) ∧
      chi q 0 = (1 - (unitInterval.toNNReal t : ℝ≥0∞))⁻¹ := by
  let q : Sym2 ℕ → unitInterval := Sym2.lift ⟨fun m n =>
    if m = n then d m else if m + 1 = n ∨ n + 1 = m then t else 0, by
      intro m n
      dsimp
      by_cases h : m = n
      · subst n; rfl
      · simp [h, Ne.symm h, or_comm]⟩
  have he (n) : q s(n,n+1) = t := by simp [q]
  have hz (m n) (hne : m ≠ n) (h : ¬ (m + 1 = n ∨ n + 1 = m)) : q s(m,n) = 0 := by
    simp [q, hne, h]
  exact ⟨q, (by intro n; simp [q]), tau_nat_eq_pow_dist q t he hz,
    chi_nat_zero_eq_geometric q t he hz⟩

end PercLib.Percolation.Bond
