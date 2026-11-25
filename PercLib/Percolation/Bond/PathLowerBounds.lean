/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 140, Q-17). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Host
public import PercLib.Probability.DeterminedIndependence

/-!
# Lower bounds for the two-point function from explicit paths

For a walk `p` from `x` to `y` write `π(p) = ∏_{e ∈ edges p} q(e)`.

* One path: `π(p) ≤ τ(x, y)`.
* Edge-disjoint paths: `1 - ∏ᵢ (1 - π(pᵢ)) ≤ τ(x, y)`.
* An exact series–parallel example: two vertices joined through `k` middle vertices, each
  pair present with probability `t`, have `τ = 1 - (1 - t²)^k`.

No countability is needed for the two lower bounds.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Open walks -/

/-- If every edge of a walk in the complete graph is open, its endpoints are connected. -/
theorem mem_conn_of_edges_subset {x y : V} (p : (⊤ : SimpleGraph V).Walk x y)
    {ω : Config V} (h : ∀ e ∈ p.edges, e ∈ ω) : ω ∈ conn x y := by
  refine ⟨p.transfer (openGraph ω) fun e he => ?_⟩
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨h e he, ?_⟩
  have := p.edges_subset_edgeSet he
  rw [SimpleGraph.edgeSet_top] at this
  exact this

/-- The event that every edge of a walk is open lies inside the connection event. -/
theorem setOf_edges_subset_subset_conn [DecidableEq V] {x y : V}
    (p : (⊤ : SimpleGraph V).Walk x y) :
    {ω : Config V | (p.edges.toFinset : Set (Sym2 V)) ⊆ ω} ⊆ conn x y := fun _ hω =>
  mem_conn_of_edges_subset p fun e he => hω (by simpa using he)

/-! ### One path -/

/-- **One path.** The probability that a walk is open bounds the two-point function. -/
theorem prod_le_tau_of_walk [DecidableEq V] (q : Sym2 V → unitInterval) {x y : V}
    (p : (⊤ : SimpleGraph V).Walk x y) :
    (∏ e ∈ p.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) ≤ tau q x y := by
  rw [← prodBernoulli_subset q p.edges.toFinset, tau]
  exact measure_mono (setOf_edges_subset_subset_conn p)

/-! ### Edge-disjoint paths -/

/-- The all-open event of a finite set of pairs is measurable. -/
theorem measurableSet_setOf_finset_subset (F : Finset (Sym2 V)) :
    MeasurableSet {ω : Config V | (F : Set (Sym2 V)) ⊆ ω} := by
  have : {ω : Config V | (F : Set (Sym2 V)) ⊆ ω} = ⋂ e ∈ F, {ω | e ∈ ω} := by
    ext ω
    simp [Set.subset_def]
  rw [this]
  exact Finset.measurableSet_biInter _ fun e _ => measurableSet_mem e

/-- An all-open event of a set of coordinates is determined by that set. -/
theorem subset_determined (F : Set (Sym2 V)) :
    ∀ ω ω' : Config V, ω ∩ F = ω' ∩ F → (F ⊆ ω ↔ F ⊆ ω') := by
  intro ω ω' h
  rw [← inter_eq_right, ← inter_eq_right (s := ω'), h]

/-- The probability that at least one of finitely many events determined by pairwise
disjoint coordinate sets occurs. -/
theorem prodBernoulli_biUnion_of_determined {ι κ : Type*} (p : ι → unitInterval)
    (s : Finset κ) {P : κ → Set ι} (hP : Set.PairwiseDisjoint (s : Set κ) P)
    {A : κ → Set (Set ι)} (hAm : ∀ k ∈ s, MeasurableSet (A k))
    (hA : ∀ k, ∀ ω ω', ω ∩ P k = ω' ∩ P k → (ω ∈ A k ↔ ω' ∈ A k)) :
    prodBernoulli p (⋃ k ∈ s, A k) = 1 - ∏ k ∈ s, (1 - prodBernoulli p (A k)) := by
  have hU : MeasurableSet (⋃ k ∈ s, A k) := Finset.measurableSet_biUnion s hAm
  have hc : (⋃ k ∈ s, A k)ᶜ = ⋂ k ∈ s, (A k)ᶜ := by simp
  have hind := prodBernoulli_biInter_of_determined p s hP (A := fun k => (A k)ᶜ)
    (fun k hk => (hAm k hk).compl) (fun k ω ω' h => not_congr (hA k ω ω' h))
  rw [← hc, prob_compl_eq_one_sub hU] at hind
  have hfin : prodBernoulli p (⋃ k ∈ s, A k) ≠ ∞ := measure_ne_top _ _
  rw [Finset.prod_congr rfl fun k hk => prob_compl_eq_one_sub (hAm k hk)] at hind
  rw [← hind, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

/-- **Edge-disjoint paths.** Pairwise edge-disjoint walks give the parallel-system lower
bound. -/
theorem one_sub_prod_le_tau_of_edgeDisjoint [DecidableEq V] (q : Sym2 V → unitInterval)
    {x y : V} {n : ℕ} (p : Fin n → (⊤ : SimpleGraph V).Walk x y)
    (hdisj : Pairwise fun i j => Disjoint (p i).edges.toFinset (p j).edges.toFinset) :
    1 - ∏ i, (1 - ∏ e ∈ (p i).edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) ≤
      tau q x y := by
  have h := prodBernoulli_biUnion_of_determined q Finset.univ
    (P := fun i => ((p i).edges.toFinset : Set (Sym2 V)))
    (fun i _ j _ hij => Finset.disjoint_coe.2 (hdisj hij))
    (A := fun i => {ω : Config V | ((p i).edges.toFinset : Set (Sym2 V)) ⊆ ω})
    (fun i _ => measurableSet_setOf_finset_subset _)
    (fun i => subset_determined _)
  simp only [prodBernoulli_subset] at h
  rw [← h, tau]
  exact measure_mono (iUnion₂_subset fun i _ => setOf_edges_subset_subset_conn (p i))

/-! ### An exact series–parallel example -/

/-- A set closed under adjacency contains everything reachable from its points. -/
theorem mem_of_reachable_of_closed {G : SimpleGraph V} {S : Set V}
    (hS : ∀ a b, G.Adj a b → a ∈ S → b ∈ S) {u v : V} (h : G.Reachable u v) (hu : u ∈ S) :
    v ∈ S := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hS _ _ hadj hu)

section SeriesParallel

open scoped Classical in
/-- **Series–parallel example.** Two vertices joined through `k` middle vertices, every pair
between a middle vertex and one of the two present with probability `t` and every other pair
absent: the two-point function is `1 - (1 - t²)^k`. -/
theorem tau_completeBipartite_bool (k : ℕ) (t : unitInterval) :
    tau (fun e => if e ∈ (completeBipartiteGraph Bool (Fin k)).edgeSet then t else 0)
        (Sum.inl false) (Sum.inl true) =
      1 - (1 - (unitInterval.toNNReal t : ℝ≥0∞) * (unitInterval.toNNReal t : ℝ≥0∞)) ^ k := by
  set G := completeBipartiteGraph Bool (Fin k) with hG
  set q : Sym2 (Bool ⊕ Fin k) → unitInterval := fun e => if e ∈ G.edgeSet then t else 0 with hq
  set x : Bool ⊕ Fin k := Sum.inl false
  set y : Bool ⊕ Fin k := Sum.inl true
  set F : Fin k → Finset (Sym2 (Bool ⊕ Fin k)) := fun m => {s(x, Sum.inr m), s(Sum.inr m, y)}
  set A : Fin k → Set (Config (Bool ⊕ Fin k)) :=
    fun m => {ω | ((F m : Finset _) : Set (Sym2 (Bool ⊕ Fin k))) ⊆ ω}
  have hFdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin k)) : Set (Fin k))
      (fun m => ((F m : Finset _) : Set (Sym2 (Bool ⊕ Fin k)))) := by
    intro m _ m' _ hmm'
    simp only [Function.onFun, F, Finset.coe_insert, Finset.coe_singleton]
    rw [Set.disjoint_left]
    intro e he he'
    simp only [mem_insert_iff, mem_singleton_iff] at he he'
    rcases he with rfl | rfl <;> rcases he' with h | h <;>
      simp [x, y] at h <;> exact hmm' h
  have hunion := prodBernoulli_biUnion_of_determined q Finset.univ hFdisj
    (A := A) (fun m _ => measurableSet_setOf_finset_subset _) (fun m => subset_determined _)
  have hA : ∀ m, prodBernoulli q (A m) =
      (unitInterval.toNNReal t : ℝ≥0∞) * (unitInterval.toNNReal t : ℝ≥0∞) := by
    intro m
    simp only [A]
    rw [prodBernoulli_subset, Finset.prod_pair (by simp [x, y])]
    have h1 : s(x, Sum.inr m) ∈ G.edgeSet := by simp [hG, x]
    have h2 : s(Sum.inr m, y) ∈ G.edgeSet := by simp [hG, y]
    simp [q, h1, h2]
  simp only [hA, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hunion
  rw [← hunion]
  -- Lower bound: each `A m` connects `x` to `y`.
  have hsub : (⋃ m ∈ (Finset.univ : Finset (Fin k)), A m) ⊆ conn x y := by
    intro ω hω
    simp only [mem_iUnion, Finset.mem_univ, exists_true_left] at hω
    obtain ⟨m, hm⟩ := hω
    have h1 : s(x, Sum.inr m) ∈ ω := hm (by simp [F])
    have h2 : s(Sum.inr m, y) ∈ ω := hm (by simp [F])
    exact conn_trans (mem_conn_of_mem (by simp [x]) h1) (mem_conn_of_mem (by simp [y]) h2)
  -- Upper bound: almost surely only bipartite pairs are open, and then a connection passes
  -- through one middle vertex.
  have hae := ae_config_subset_host G q (fun e he => by simp [q, he])
  refine le_antisymm ?_ (measure_mono hsub)
  rw [tau]
  refine measure_mono_ae ?_
  filter_upwards [hae] with ω hω hconn
  simp only [mem_iUnion, Finset.mem_univ, exists_true_left]
  by_contra hno
  simp only [not_exists] at hno
  have hclosed : ∀ a b, (openGraph ω).Adj a b →
      a ∈ {v | v = x ∨ ∃ m, v = Sum.inr m ∧ s(x, Sum.inr m) ∈ ω} →
        b ∈ {v | v = x ∨ ∃ m, v = Sum.inr m ∧ s(x, Sum.inr m) ∈ ω} := by
    intro a b hab ha
    rw [openGraph_adj_iff] at hab
    have hGab : G.Adj a b := (SimpleGraph.mem_edgeSet G).1 (hω hab.1)
    rcases ha with rfl | ⟨m, rfl, hm⟩
    · rcases b with b | m
      · simp [hG, x] at hGab
      · exact Or.inr ⟨m, rfl, hab.1⟩
    · rcases b with c | m'
      · cases c
        · exact Or.inl rfl
        · exfalso
          refine hno m ?_
          intro e he
          simp only [F, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
            mem_singleton_iff] at he
          rcases he with rfl | rfl
          · exact hm
          · exact hab.1
      · simp [hG] at hGab
  have hy := mem_of_reachable_of_closed hclosed hconn (Or.inl rfl)
  rcases hy with h | ⟨m, h, -⟩ <;> simp [x, y] at h

end SeriesParallel

/-! ### Non-vacuity -/

open scoped Classical in
/-- Two parallel middle vertices with `t = 1/2`: `τ = 1 - (3/4)^2`. -/
example : tau (fun e => if e ∈ (completeBipartiteGraph Bool (Fin 2)).edgeSet then
      (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      (Sum.inl false) (Sum.inl true) =
    1 - (1 - (unitInterval.toNNReal ⟨1 / 2, by norm_num, by norm_num⟩ : ℝ≥0∞) *
      (unitInterval.toNNReal ⟨1 / 2, by norm_num, by norm_num⟩ : ℝ≥0∞)) ^ 2 :=
  tau_completeBipartite_bool 2 ⟨1 / 2, by norm_num, by norm_num⟩

end PercLib.Percolation.Bond

end
