/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New site-percolation proofs using the merged PercLib bond path-counting theorems
and mathlib walks. No upstream proof copied.
-/
module

public import PercLib.Percolation.Bond.SelfAvoiding
public import Mathlib.Order.SuccPred.Int

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal Classical

namespace PercLib.Models.Site
variable {V : Type*}

/-- Every vertex of an open-site walk is open if its starting vertex is open.
The starting-vertex hypothesis also covers the length-zero walk. -/
theorem walk_support_subset_open {G : SimpleGraph V} {ω : Set V} {x y : V}
    (r : (openSiteGraph G ω).Walk x y) (hx : x ∈ ω) :
    ∀ z ∈ r.support, z ∈ ω := by
  induction r with
  | nil => simpa using hx
  | @cons a b c hab r ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact ih ((openSiteGraph_adj_iff' G ω a b).mp hab).2.2 z hz

/-- An infinite site cluster contains open simple paths of every finite length. -/
theorem exists_path_length_of_siteCluster_infinite (G : SimpleGraph V) [G.LocallyFinite]
    {ω : Set V} {x : V} (hinf : (siteCluster G ω x).Infinite) (n : ℕ) :
    ∃ y, ∃ r : G.Path x y, r.1.length = n ∧ ∀ z ∈ r.1.support, z ∈ ω := by
  have hhost : openSiteGraph G ω ≤ G := fun a b h =>
    ((openSiteGraph_adj_iff' G ω a b).mp h).1
  obtain ⟨y, hy, hny⟩ := hinf.exists_notMem_finite (finite_bounded_walk_endpoints G x n)
  obtain ⟨r, hr⟩ := hy.2.exists_isPath
  have hn : n ≤ r.length := by
    by_contra h
    exact hny ⟨r.mapLe hhost, by simpa using (Nat.le_of_lt (Nat.lt_of_not_ge h))⟩
  let t := r.take n
  refine ⟨r.getVert n, ⟨t.mapLe hhost, (hr.take n).mapLe hhost⟩, ?_, ?_⟩
  · simp [t, hn]
  · simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using
      walk_support_subset_open t hy.1

/-- A length n+1 site path has n+2 distinct vertices, all of which must be open. -/
theorem siteBernoulli_exists_path_length_le (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (w : V → unitInterval) (p : unitInterval)
    (hw : ∀ v, w v ≤ p) (x : V) (n : ℕ) :
    siteBernoulli w {ω | ∃ y, ∃ r : G.Path x y, r.1.length = n+1 ∧
      ∀ z ∈ r.1.support, z ∈ ω} ≤
      (Δ * (Δ-1)^n : ℕ) * (unitInterval.toNNReal p : ℝ≥0∞)^(n+2) := by
  classical
  let P := {r : Σ y, G.Path x y // r.2.1.length = n+1}
  have hcard := finite_card_paths_length G hΔ x n
  let : Finite P := hcard.1
  let : Fintype P := Fintype.ofFinite P
  have heq : {ω | ∃ y, ∃ r : G.Path x y, r.1.length = n+1 ∧
      ∀ z ∈ r.1.support, z ∈ ω} =
      ⋃ r : P, {ω : Set V | (r.1.2.1.support.toFinset : Set V) ⊆ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y,r,hn,hr⟩
      exact ⟨⟨⟨y,r⟩,hn⟩, fun z hz => hr z (List.mem_toFinset.mp hz)⟩
    · rintro ⟨r,hr⟩
      exact ⟨r.1.1,r.1.2,r.2, fun z hz => hr (List.mem_toFinset.mpr hz)⟩
  rw [heq]
  calc
    _ ≤ ∑' r : P, siteBernoulli w {ω | (r.1.2.1.support.toFinset : Set V) ⊆ ω} :=
      measure_iUnion_le _
    _ = ∑' r : P, ∏ z ∈ r.1.2.1.support.toFinset, (unitInterval.toNNReal (w z) : ℝ≥0∞) := by
      simp only [siteBernoulli, prodBernoulli_subset]
    _ ≤ ∑' _r : P, (unitInterval.toNNReal p : ℝ≥0∞)^(n+2) := by
      apply ENNReal.tsum_le_tsum
      intro r
      calc
        _ ≤ ∏ _z ∈ r.1.2.1.support.toFinset, (unitInterval.toNNReal p : ℝ≥0∞) :=
          Finset.prod_le_prod (fun z _ => ENNReal.coe_le_coe.mpr (hw z))
        _ = _ := by
          rw [Finset.prod_const, List.toFinset_card_of_nodup r.1.2.2.support_nodup,
            SimpleGraph.Walk.length_support, r.2]
    _ = (Nat.card P : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞)^(n+2) := by
      simp [tsum_fintype, Nat.card_eq_fintype_card]
    _ ≤ _ := by
      gcongr
      exact_mod_cast hcard.2

/-- The self-avoiding-path criterion, with natural subtraction for degrees zero and one. -/
theorem siteBernoulli_siteInfinite_eq_zero_of_degree_le_ennreal
    (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (w : V → unitInterval) (p : unitInterval) (hw : ∀ v, w v ≤ p)
    (hp : ((Δ-1 : ℕ) : ℝ≥0∞) * unitInterval.toNNReal p < 1) (x : V) :
    siteBernoulli w {ω | (siteCluster G ω x).Infinite} = 0 := by
  apply ENNReal.eq_zero_of_le_mul_pow (ε := (Δ : ℝ≥0) * unitInterval.toNNReal p ^ 2) hp
  intro n
  calc
    _ ≤ siteBernoulli w {ω | ∃ y, ∃ r : G.Path x y, r.1.length = n+1 ∧
        ∀ z ∈ r.1.support, z ∈ ω} :=
      measure_mono (fun _ hi => exists_path_length_of_siteCluster_infinite G hi (n+1))
    _ ≤ (Δ * (Δ-1)^n : ℕ) * (unitInterval.toNNReal p : ℝ≥0∞)^(n+2) :=
      siteBernoulli_exists_path_length_le G hΔ w p hw x n
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_pow, ENNReal.coe_mul, ENNReal.coe_natCast,
        ENNReal.coe_pow, mul_pow, pow_add]
      ring

/-- If (Δ−1)p<1, site percolation on a graph of maximum degree Δ has no infinite
cluster at a specified root. No countability of the vertex type is needed. -/
theorem siteBernoulli_siteInfinite_eq_zero_of_degree_le
    (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (w : V → unitInterval) (p : unitInterval) (hw : ∀ v, w v ≤ p)
    (hp : ((Δ : ℝ)-1) * (p : ℝ) < 1) (x : V) :
    siteBernoulli w {ω | (siteCluster G ω x).Infinite} = 0 := by
  apply siteBernoulli_siteInfinite_eq_zero_of_degree_le_ennreal G hΔ w p hw _ x
  by_cases hΔ0 : Δ = 0
  · simp [hΔ0]
  · have hΔ1 : 1 ≤ Δ := Nat.one_le_iff_ne_zero.mpr hΔ0
    have hp' : (((Δ-1 : ℕ) : ℝ≥0) * unitInterval.toNNReal p : ℝ≥0) < 1 := by
      change ((Δ-1 : ℕ) : ℝ) * (p : ℝ) < 1
      simpa [Nat.cast_sub hΔ1] using hp
    exact_mod_cast hp'

/-- Countably many roots may be treated simultaneously. -/
theorem ae_all_siteClusters_finite_of_degree_le [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (w : V → unitInterval) (p : unitInterval) (hw : ∀ v, w v ≤ p)
    (hp : ((Δ : ℝ)-1) * (p : ℝ) < 1) :
    ∀ᵐ ω ∂siteBernoulli w, ∀ x, (siteCluster G ω x).Finite := by
  apply ae_all_iff.mpr
  intro x
  rw [ae_iff]
  simpa only [Set.not_finite] using
    siteBernoulli_siteInfinite_eq_zero_of_degree_le G hΔ w p hw hp x

/-- A finite cover of each lattice neighbour set by signed coordinate steps.
This local degree bound avoids a dependency on the pending Q-32 lattice package. -/
private theorem lattice_neighbors_subset (d : ℕ) (x : LatticeSite d) :
    (zdGraph d).neighborSet x ⊆ Set.range
      (fun t : Fin d × Bool => Function.update x t.1 (x t.1 + if t.2 then 1 else -1)) := by
  intro y hy
  rcases (SimpleGraph.hasse_adj.mp hy) with h | h
  · obtain ⟨i, z, hz, rfl⟩ := Pi.covBy_iff_exists_right_eq.mp h
    have hz' : x i + 1 = z := Order.covBy_iff_add_one_eq.mp hz
    exact ⟨(i, true), by simp [hz']⟩
  · obtain ⟨i, z, hz, rfl⟩ := Pi.covBy_iff_exists_left_eq.mp h
    have hz' : z + 1 = x i := Order.covBy_iff_add_one_eq.mp hz
    exact ⟨(i, false), by simp; congr 1; omega⟩

/-- Local finiteness and the bound 2d, packaged as an existence theorem so that
this proof module introduces no global instance. -/
private theorem exists_lattice_degree_bound (d : ℕ) :
    ∃ h : (zdGraph d).LocallyFinite, letI := h; ∀ x, (zdGraph d).degree x ≤ 2*d := by
  classical
  have hfin (x : LatticeSite d) : ((zdGraph d).neighborSet x).Finite :=
    (Set.finite_range _).subset (lattice_neighbors_subset d x)
  let h : (zdGraph d).LocallyFinite := fun x => (hfin x).fintype
  refine ⟨h, ?_⟩
  intro x
  rw [← SimpleGraph.ncard_neighborSet]
  calc
    _ ≤ (Set.range (fun t : Fin d × Bool =>
        Function.update x t.1 (x t.1 + if t.2 then 1 else -1))).ncard :=
      Set.ncard_le_ncard (lattice_neighbors_subset d x) (Set.finite_range _)
    _ ≤ Nat.card (Fin d × Bool) := Finite.card_range_le _
    _ = 2*d := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

/-- Subcritical site percolation on the nearest-neighbour integer lattice. -/
theorem thetaSite_eq_zero_of_lt_inv {d : ℕ} (hd : 1 ≤ d) (p : unitInterval)
    (hp : (p : ℝ) < 1 / (2*(d : ℝ)-1)) : thetaSite d p = 0 := by
  obtain ⟨h, hdegree⟩ := exists_lattice_degree_bound d
  let := h
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) < 2*d-1 := by linarith
  have hmul := (lt_div_iff₀ hpos).mp hp
  have hz := siteBernoulli_siteInfinite_eq_zero_of_degree_le (zdGraph d) hdegree
    (fun _ => p) p (fun _ => le_rfl) (by push_cast; nlinarith) 0
  simp only [thetaSite, thetaSiteOn, measureReal_def, hz, ENNReal.toReal_zero]

/-- The elementary lower bound for the site critical parameter, including d=1. -/
theorem inv_le_criticalProbSite {d : ℕ} (hd : 1 ≤ d) :
    1 / (2*(d : ℝ)-1) ≤ criticalProbSite d := by
  apply le_csInf (show ({p : ℝ | ∃ h : p ∈ unitInterval,
    0 < thetaSite d ⟨p,h⟩} ∪ {1}).Nonempty from ⟨1, Or.inr rfl⟩)
  rintro p (⟨hp, htheta⟩ | hp)
  · by_contra hn
    have hz := thetaSite_eq_zero_of_lt_inv hd ⟨p,hp⟩ (lt_of_not_ge hn)
    rw [hz] at htheta
    exact (lt_irrefl _ htheta)
  · have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hpos : (0 : ℝ) < 2*d-1 := by linarith
    have hp' : p = 1 := hp
    rw [hp']
    apply (div_le_iff₀ hpos).mpr
    linarith

-- The closed-root convention is respected even for the zero-length path.
example (G : SimpleGraph V) [G.LocallyFinite] {ω : Set V} {x : V}
    (hi : (siteCluster G ω x).Infinite) : x ∈ ω := by
  obtain ⟨y,r,_,hr⟩ := exists_path_length_of_siteCluster_infinite G hi 0
  exact hr x r.1.start_mem_support

-- Degree zero and one allow probability one; their clusters are still finite.
example : siteBernoulli (fun _ : ℕ => 1) {ω | (siteCluster ⊥ ω 0).Infinite} = 0 := by
  let : (⊥ : SimpleGraph ℕ).LocallyFinite := fun v =>
    Fintype.ofFinset (∅ : Finset ℕ) (by intro w; simp)
  exact siteBernoulli_siteInfinite_eq_zero_of_degree_le (⊥ : SimpleGraph ℕ)
    (Δ := 0) (by intro v; simp) _ 1 (fun _ => le_rfl) (by norm_num) 0

example : siteBernoulli (fun _ : Bool => 1) {ω | (siteCluster ⊤ ω false).Infinite} = 0 :=
  siteBernoulli_siteInfinite_eq_zero_of_degree_le (⊤ : SimpleGraph Bool)
    (Δ := 1) (by intro v; simp) _ 1 (fun _ => le_rfl) (by norm_num) false

example : criticalProbSite 1 = 1 := by
  apply le_antisymm (criticalProbSite_mem_Icc 1).2
  convert inv_le_criticalProbSite (d := 1) (by norm_num) using 1; norm_num

example : thetaSite 2 ⟨1/4, by constructor <;> norm_num⟩ = 0 := by
  apply thetaSite_eq_zero_of_lt_inv (by norm_num)
  norm_num

end PercLib.Models.Site
