/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 194, Q-34). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.VolumeTails
public import PercLib.Probability.Cylinder
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Exponential tails of the cluster size on bounded-degree graphs

If the cluster of `x` has at least `n + 1` vertices then the open graph contains a closed walk
from `x` of length `2n` visiting at least `n + 1` vertices (grow it by inserting detours to new
vertices). Such a walk uses at least `n` distinct pairs, all open. A graph of maximal degree
`Δ` has at most `Δ^{2n}` closed walks of length `2n` from `x`, so

`P(|K_x| ≥ n + 1) ≤ (Δ² p)^n`

when the profile is supported on the graph (off the diagonal) and at most `p` on its edges.
The closed walks play the role of the depth-first encodings of spanning trees.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Walks -/

section Walks

variable {H : SimpleGraph V}

/-- A walk visits at most one more vertex than it has distinct edges. -/
theorem card_support_toFinset_le [DecidableEq V] {u v : V} (w : H.Walk u v) :
    w.support.toFinset.card ≤ w.edges.toFinset.card + 1 := by
  induction w with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.edges_cons, List.toFinset_cons,
      List.toFinset_cons]
    by_cases ha : a ∈ p.support
    · rw [Finset.insert_eq_of_mem (List.mem_toFinset.2 ha)]
      exact ih.trans (Nat.add_le_add_right (Finset.card_le_card (Finset.subset_insert _ _)) 1)
    · have he : s(a, b) ∉ p.edges := fun h => ha (p.fst_mem_support_of_mem_edges h)
      rw [Finset.card_insert_of_notMem (by simpa using ha),
        Finset.card_insert_of_notMem (by simpa using he)]
      omega

/-- A walk from inside a set to outside it crosses an edge leaving the set. -/
theorem exists_adj_mem_notMem {S : Set V} {u v : V} (w : H.Walk u v) (hu : u ∈ S)
    (hv : v ∉ S) : ∃ a ∈ S, ∃ b ∉ S, H.Adj a b := by
  induction w with
  | nil => exact absurd hu hv
  | @cons a b c hab p ih =>
    by_cases hb : b ∈ S
    · exact ih hb hv
    · exact ⟨a, hu, b, hb, hab⟩

/-- Inserting a detour `a → b → a` into a walk at a visited vertex `a`. -/
theorem exists_walk_insert_detour [DecidableEq V] {u v a b : V} (w : H.Walk u v)
    (ha : a ∈ w.support) (hab : H.Adj a b) :
    ∃ w' : H.Walk u v, w'.length = w.length + 2 ∧
      insert b w.support.toFinset ⊆ w'.support.toFinset := by
  refine ⟨(w.takeUntil a ha).append
    (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hab.symm (w.dropUntil a ha))), ?_, ?_⟩
  · conv_rhs => rw [← w.take_spec ha]
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
    ring
  · intro z hz
    rw [Finset.mem_insert, List.mem_toFinset] at hz
    rw [List.mem_toFinset, SimpleGraph.Walk.mem_support_append_iff]
    rcases hz with rfl | hz
    · right
      simp
    · rw [← w.take_spec ha, SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · right
        simp [hz]

end Walks

/-- **Closed walks grow inside a large cluster.** If the cluster of `x` has at least `n + 1`
vertices, then for every `k ≤ n` there is a closed open walk from `x` of length `2k` visiting
at least `k + 1` vertices. -/
theorem exists_closed_walk_of_le_encard_cluster [DecidableEq V] (ω : Config V) (x : V) {n : ℕ}
    (hn : ((n + 1 : ℕ) : ℕ∞) ≤ (cluster ω x).encard) :
    ∀ k ≤ n, ∃ w : (openGraph ω).Walk x x, w.length = 2 * k ∧
      k + 1 ≤ w.support.toFinset.card := by
  intro k hk
  induction k with
  | zero => exact ⟨SimpleGraph.Walk.nil, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨w, hlen, hcard⟩ := ih (by omega)
    obtain ⟨S, hS⟩ : ∃ S, S = w.support.toFinset := ⟨_, rfl⟩
    rw [← hS] at hcard
    have hxS : x ∈ (S : Set V) := by simp [hS, w.start_mem_support]
    by_cases hsub : cluster ω x ⊆ (S : Set V)
    · -- The walk already visits enough vertices; detour along any edge at `x`.
      have hbig : n + 1 ≤ S.card := by
        have := hn.trans (Set.encard_le_encard hsub)
        rw [Set.encard_coe_eq_coe_finsetCard] at this
        exact_mod_cast this
      have hcl : ¬ cluster ω x ⊆ ({x} : Set V) := by
        intro h
        have := hn.trans (Set.encard_le_encard h)
        rw [Set.encard_singleton] at this
        have : n + 1 ≤ 1 := by exact_mod_cast this
        omega
      obtain ⟨y, hy, hyx⟩ := Set.not_subset.1 hcl
      obtain ⟨p⟩ := hy
      obtain ⟨a, ha, b, -, hab⟩ := exists_adj_mem_notMem p (Set.mem_singleton x) hyx
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨w', hlen', hsub'⟩ := exists_walk_insert_detour w w.start_mem_support hab
      rw [← hS] at hsub'
      refine ⟨w', by rw [hlen', hlen]; ring, ?_⟩
      have := Finset.card_le_card ((Finset.subset_insert b S).trans hsub')
      omega
    · obtain ⟨y, hy, hyS⟩ := Set.not_subset.1 hsub
      obtain ⟨p⟩ := hy
      obtain ⟨a, ha, b, hb, hab⟩ := exists_adj_mem_notMem p hxS hyS
      have ha' : a ∈ w.support := by simpa [hS] using ha
      obtain ⟨w', hlen', hsub'⟩ := exists_walk_insert_detour w ha' hab
      rw [← hS] at hsub'
      refine ⟨w', by rw [hlen', hlen]; ring, ?_⟩
      have h1 := Finset.card_le_card hsub'
      rw [Finset.card_insert_of_notMem (Finset.mem_coe.not.1 hb)] at h1
      omega

/-! ### Counting walks -/

/-- A graph of maximal degree `Δ` has at most `Δ^m` walks of length `m` between two given
vertices. -/
theorem card_finsetWalkLength_le [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (m : ℕ) (u v : V) :
    (G.finsetWalkLength m u v).card ≤ Δ ^ m := by
  induction m generalizing u with
  | zero =>
    simp only [SimpleGraph.finsetWalkLength, pow_zero]
    split_ifs with h
    · subst h; simp
    · simp
  | succ m ih =>
    simp only [SimpleGraph.finsetWalkLength]
    refine (Finset.card_biUnion_le).trans ?_
    simp only [Finset.card_map]
    calc ∑ w : G.neighborSet u, (G.finsetWalkLength m w v).card
        ≤ ∑ _w : G.neighborSet u, Δ ^ m := Finset.sum_le_sum fun w _ => ih w
      _ = Fintype.card (G.neighborSet u) * Δ ^ m := by simp
      _ ≤ Δ * Δ ^ m := by
        rw [SimpleGraph.card_neighborSet_eq_degree]
        exact Nat.mul_le_mul_right _ (hΔ u)
      _ = Δ ^ (m + 1) := by ring

/-! ### The tail bound -/

/-- Under a profile supported on `G` off the diagonal, almost surely every open non-diagonal
pair is an edge of `G`. -/
theorem ae_mem_edgeSet_of_offDiag_supported [Countable V] (G : SimpleGraph V)
    {q : Sym2 V → unitInterval} (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) :
    ∀ᵐ ω ∂law q, ∀ e ∈ ω, ¬ e.IsDiag → e ∈ G.edgeSet := by
  classical
  have he (e : Sym2 V) : ∀ᵐ ω ∂law q, e ∈ ω → ¬ e.IsDiag → e ∈ G.edgeSet := by
    by_cases h : e.IsDiag ∨ e ∈ G.edgeSet
    · exact Filter.Eventually.of_forall fun _ _ hd => h.resolve_left hd
    · rw [not_or] at h
      have hz : law q {ω | e ∈ ω} = 0 := by
        simpa [law, hoff e h.1 h.2] using prodBernoulli_setOf_mem q e
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) hz
      simp only [mem_ofPred_eq, not_forall] at hω
      obtain ⟨hω, -, -⟩ := hω
      exact hω
  filter_upwards [ae_all_iff.2 he] with ω hω e he' hd
  exact hω e he' hd

/-- **Tree counting.** On a graph of maximal degree `Δ`, with a profile supported on the graph
off the diagonal and at most `p` on its edges, `P(|K_x| ≥ n + 1) ≤ (Δ² p)^n`. -/
theorem law_le_encard_cluster_le [Countable V] (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    (x : V) (n : ℕ) :
    law q {ω | ((n + 1 : ℕ) : ℕ∞) ≤ (cluster ω x).encard} ≤
      ((Δ : ℝ≥0∞) ^ 2 * (unitInterval.toNNReal p : ℝ≥0∞)) ^ n := by
  classical
  set W := (G.finsetWalkLength (2 * n) x x).filter fun w => n + 1 ≤ w.support.toFinset.card
  set N := {ω : Config V | ¬ ∀ e ∈ ω, ¬ e.IsDiag → e ∈ G.edgeSet}
  have hN : law q N = 0 := by
    have := ae_mem_edgeSet_of_offDiag_supported G hoff
    rwa [ae_iff] at this
  have hsub : {ω : Config V | ((n + 1 : ℕ) : ℕ∞) ≤ (cluster ω x).encard} ⊆
      N ∪ ⋃ w ∈ W, {ω : Config V | (w.edges.toFinset : Set (Sym2 V)) ⊆ ω} := by
    intro ω hω
    by_cases hgood : ∀ e ∈ ω, ¬ e.IsDiag → e ∈ G.edgeSet
    · right
      obtain ⟨w, hlen, hcard⟩ := exists_closed_walk_of_le_encard_cluster ω x hω n le_rfl
      have hedges : ∀ e ∈ w.edges, e ∈ G.edgeSet := by
        intro e he
        have h1 := w.edges_subset_edgeSet he
        rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1
        exact hgood e h1.1 h1.2
      set w' := w.transfer G hedges
      simp only [mem_iUnion]
      refine ⟨w', ?_, ?_⟩
      · simp only [W, Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff, w',
          SimpleGraph.Walk.length_transfer, SimpleGraph.Walk.support_transfer]
        exact ⟨hlen, hcard⟩
      · intro e he
        simp only [w', SimpleGraph.Walk.edges_transfer, List.coe_toFinset,
          mem_ofPred_eq] at he
        have h1 := w.edges_subset_edgeSet he
        rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1
        exact h1.1
    · exact Or.inl hgood
  have hterm : ∀ w ∈ W, law q {ω : Config V | (w.edges.toFinset : Set (Sym2 V)) ⊆ ω} ≤
      (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
    intro w hw
    simp only [W, Finset.mem_filter, SimpleGraph.mem_finsetWalkLength_iff] at hw
    rw [law, prodBernoulli_subset]
    have hp1 : (unitInterval.toNNReal p : ℝ≥0∞) ≤ 1 := by
      exact_mod_cast (show unitInterval.toNNReal p ≤ 1 from p.2.2)
    calc ∏ e ∈ w.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)
        ≤ ∏ _e ∈ w.edges.toFinset, (unitInterval.toNNReal p : ℝ≥0∞) := by
          refine Finset.prod_le_prod fun e he => ?_
          exact_mod_cast (show unitInterval.toNNReal (q e) ≤ unitInterval.toNNReal p from
            hle e (w.edges_subset_edgeSet (List.mem_toFinset.1 he)))
      _ = (unitInterval.toNNReal p : ℝ≥0∞) ^ w.edges.toFinset.card := Finset.prod_const _
      _ ≤ (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
          refine pow_le_pow_of_le_one (by simp) hp1 ?_
          have := card_support_toFinset_le w
          omega
  calc law q {ω | ((n + 1 : ℕ) : ℕ∞) ≤ (cluster ω x).encard}
      ≤ law q N + law q (⋃ w ∈ W, {ω : Config V | (w.edges.toFinset : Set (Sym2 V)) ⊆ ω}) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ 0 + ∑ w ∈ W, law q {ω : Config V | (w.edges.toFinset : Set (Sym2 V)) ⊆ ω} := by
        rw [hN]
        gcongr
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ W, (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
        rw [zero_add]
        exact Finset.sum_le_sum hterm
    _ = W.card * (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by simp
    _ ≤ ((Δ ^ (2 * n) : ℕ) : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) ^ n := by
        gcongr
        exact (Finset.card_filter_le _ _).trans (card_finsetWalkLength_le G hΔ _ x x)
    _ = ((Δ : ℝ≥0∞) ^ 2 * (unitInterval.toNNReal p : ℝ≥0∞)) ^ n := by
        push_cast
        ring

/-- **Susceptibility.** Under the same hypotheses, `χ(x) ≤ (1 - Δ² p)⁻¹`; it is finite when
`Δ² p < 1`. -/
theorem chi_le_inv_one_sub_of_degree_le [Countable V] (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    (x : V) :
    chi q x ≤ (1 - (Δ : ℝ≥0∞) ^ 2 * (unitInterval.toNNReal p : ℝ≥0∞))⁻¹ := by
  rw [chi_eq_tsum_law_le_encard, ← ENNReal.tsum_geometric]
  exact ENNReal.tsum_le_tsum fun n => law_le_encard_cluster_le G hΔ q p hoff hle x n

/-! ### Non-vacuity -/

/-- The complete graph on `Fin 3` has maximal degree `2`, and every profile bounded by `p`
satisfies the hypotheses. -/
example (p : unitInterval) (n : ℕ) :
    law (fun _ : Sym2 (Fin 3) => p) {ω | ((n + 1 : ℕ) : ℕ∞) ≤ (cluster ω 0).encard} ≤
      (((2 : ℕ) : ℝ≥0∞) ^ 2 * (unitInterval.toNNReal p : ℝ≥0∞)) ^ n :=
  law_le_encard_cluster_le (⊤ : SimpleGraph (Fin 3)) (fun v => Nat.lt_succ_iff.1 (by
    simp)) _ p
    (fun e hd he => absurd (SimpleGraph.edgeSet_top ▸ hd : e ∈ (⊤ : SimpleGraph (Fin 3)).edgeSet) he)
    (fun _ _ => le_rfl) 0 n

end PercLib.Percolation.Bond

end
