/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New cluster-tail glue using the existing finite-open-path witness API in
PercLib.Probability.OpenEventHarris and mathlib's finite subsets and measure
continuity. No upstream proof is copied and no tightness bound is asserted.
-/
module

public import PercLib.Probability.OpenEventHarris
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A finite-domain volume threshold is witnessed by the required number of distinct roots. -/
theorem cluster_tail_iff_exists_finset (ω : Config V) (v : V) (Λ : Finset V) (k : ℕ) :
    k ≤ (cluster ω v ∩ (Λ : Set V)).ncard ↔
      ∃ S : Finset V, S ⊆ Λ ∧ S.card = k ∧ ∀ x ∈ S, ω ∈ conn v x := by
  constructor
  · intro h
    obtain ⟨S, hS, hcard⟩ := Set.exists_subset_card_eq h
    have hfin : S.Finite := Λ.finite_toSet.subset (fun x hx => (hS hx).2)
    refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
    · intro x hx
      exact (hS (hfin.mem_toFinset.mp hx)).2
    · simpa only [Set.ncard_eq_toFinset_card S hfin] using hcard
    · intro x hx
      exact (hS (hfin.mem_toFinset.mp hx)).1
  · rintro ⟨S, hS, rfl, hc⟩
    have hs : (S : Set V) ⊆ cluster ω v ∩ (Λ : Set V) :=
      fun x hx => ⟨hc x hx, hS hx⟩
    simpa using Set.ncard_le_ncard hs (Λ.finite_toSet.subset inter_subset_right)

/-- The tail event is a finite-subset union of intersections of connection events. -/
theorem cluster_tail_eq_iUnion (v : V) (Λ : Finset V) (k : ℕ) :
    {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard} =
      ⋃ S ∈ {S : Finset V | S ⊆ Λ ∧ S.card = k}, ⋂ x ∈ S, conn v x := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
  rw [cluster_tail_iff_exists_finset]
  aesop

/-- Cluster-tail events are increasing in the configuration. -/
theorem isUpperSet_cluster_tail (v : V) (Λ : Finset V) (k : ℕ) :
    IsUpperSet {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard} := by
  intro ω ω' h hω
  obtain ⟨S, hS, hc, hconn⟩ := (cluster_tail_iff_exists_finset ω v Λ k).mp hω
  exact (cluster_tail_iff_exists_finset ω' v Λ k).mpr
    ⟨S, hS, hc, fun x hx => conn_mono h (hconn x hx)⟩

/-- The full event is measurable on countable vertex types. -/
theorem measurableSet_cluster_tail [Countable V] (v : V) (Λ : Finset V) (k : ℕ) :
    MeasurableSet {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard} := by
  rw [cluster_tail_eq_iUnion]
  exact MeasurableSet.biUnion (Set.to_countable _) fun S _ =>
    MeasurableSet.iInter fun x => MeasurableSet.iInter fun _ => measurableSet_conn v x

/-- Finitely many open connections share a finite open-edge witness. -/
theorem exists_finset_of_forall_conn {ω : Config V} (v : V) (S : Finset V)
    (h : ∀ x ∈ S, ω ∈ conn v x) :
    ∃ F : Finset (Sym2 V), (F : Config V) ⊆ ω ∧ ∀ x ∈ S, (F : Config V) ∈ conn v x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert x S hx ih =>
    obtain ⟨F, hF, hcF⟩ := exists_finset_of_mem_conn (h x (Finset.mem_insert_self _ _))
    obtain ⟨H, hH, hcH⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    refine ⟨F ∪ H, ?_, ?_⟩
    · simpa only [Finset.coe_union] using Set.union_subset hF hH
    rw [Finset.coe_union]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact conn_mono Set.subset_union_left hcF
    · exact conn_mono Set.subset_union_right (hcH y hy)

/-- Every finite-domain cluster tail occurrence has a finite open-edge witness. -/
theorem exists_finset_of_cluster_tail {ω : Config V} (v : V) (Λ : Finset V) (k : ℕ)
    (h : k ≤ (cluster ω v ∩ (Λ : Set V)).ncard) :
    ∃ F : Finset (Sym2 V), (F : Config V) ⊆ ω ∧
      k ≤ (cluster (F : Config V) v ∩ (Λ : Set V)).ncard := by
  obtain ⟨S, hS, hc, hconn⟩ := (cluster_tail_iff_exists_finset ω v Λ k).mp h
  obtain ⟨F, hF, hcF⟩ := exists_finset_of_forall_conn v S hconn
  exact ⟨F, hF, (cluster_tail_iff_exists_finset _ v Λ k).mpr ⟨S, hS, hc, hcF⟩⟩

/-- Increasing finite-edge restrictions give increasing cluster-tail events. -/
theorem monotone_cluster_tail_restrict (v : V) (Λ : Finset V) (k : ℕ)
    {E : ℕ → Finset (Sym2 V)} (hE : Monotone E) :
    Monotone (fun n => {ω : Config V |
      k ≤ (cluster (ω ∩ (E n : Set (Sym2 V))) v ∩ (Λ : Set V)).ncard}) := by
  intro n m hnm ω hω
  exact isUpperSet_cluster_tail v Λ k (Set.inter_subset_inter_right _ (hE hnm)) hω

/-- Any increasing exhaustive finite-edge sequence recovers the full tail event. -/
theorem cluster_tail_eq_iUnion_restrict (v : V) (Λ : Finset V) (k : ℕ)
    {E : ℕ → Finset (Sym2 V)} (hE : Monotone E) (hcover : ∀ e, ∃ n, e ∈ E n) :
    {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard} =
      ⋃ n, {ω : Config V |
        k ≤ (cluster (ω ∩ (E n : Set (Sym2 V))) v ∩ (Λ : Set V)).ncard} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro h
    obtain ⟨F, hF, hc⟩ := exists_finset_of_cluster_tail v Λ k h
    have hf : (F : Set (Sym2 V)) ⊆ ⋃ n, (E n : Set (Sym2 V)) :=
      fun e _ => Set.mem_iUnion.mpr (hcover e)
    have hm : Monotone (fun n => (E n : Set (Sym2 V))) := fun _ _ h => hE h
    obtain ⟨n, hn⟩ := hm.directed_le.exists_mem_subset_of_finset_subset_biUnion hf
    exact ⟨n, isUpperSet_cluster_tail v Λ k (Set.subset_inter hF hn) hc⟩
  · rintro ⟨n, hn⟩
    exact isUpperSet_cluster_tail v Λ k Set.inter_subset_left hn

/-- Probability convergence along any increasing exhaustive finite-edge restriction. -/
theorem tendsto_cluster_tail_probability (q : Sym2 V → unitInterval)
    (v : V) (Λ : Finset V) (k : ℕ) {E : ℕ → Finset (Sym2 V)}
    (hE : Monotone E) (hcover : ∀ e, ∃ n, e ∈ E n) :
    Filter.Tendsto (fun n => law q {ω : Config V |
      k ≤ (cluster (ω ∩ (E n : Set (Sym2 V))) v ∩ (Λ : Set V)).ncard}) Filter.atTop
      (nhds (law q {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard})) := by
  have h := tendsto_measure_iUnion_atTop (μ := law q) (monotone_cluster_tail_restrict v Λ k hE)
  simpa only [← cluster_tail_eq_iUnion_restrict v Λ k hE hcover, Function.comp_def] using h

/-- A zero threshold is the certain event, including an empty domain. -/
theorem cluster_tail_zero (v : V) (Λ : Finset V) :
    {ω : Config V | 0 ≤ (cluster ω v ∩ (Λ : Set V)).ncard} = Set.univ := by simp

/-- A threshold larger than the domain is impossible. -/
theorem cluster_tail_gt_card (v : V) (Λ : Finset V) (k : ℕ) (hk : Λ.card < k) :
    {ω : Config V | k ≤ (cluster ω v ∩ (Λ : Set V)).ncard} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω h
  have he := Set.ncard_inter_le_ncard_right (cluster ω v) (Λ : Set V) Λ.finite_toSet
  simp only [Set.ncard_coe_finset] at he
  exact (hk.not_ge (h.trans he))

-- The root contributes even in the empty configuration.
example (v : V) : 1 ≤ (cluster (∅ : Config V) v ∩ ({v} : Set V)).ncard := by
  simp [cluster_empty]

-- Reaching both Bool vertices requires an actual open connection.
example : 2 ≤ (cluster ({s(false, true)} : Config Bool) false ∩
    (({false, true} : Finset Bool) : Set Bool)).ncard := by
  apply (cluster_tail_iff_exists_finset _ false {false, true} 2).mpr
  refine ⟨{false, true}, subset_rfl, by decide, ?_⟩
  intro x hx
  cases x
  · exact SimpleGraph.Reachable.refl _
  · exact mem_conn_of_mem (by decide) (by simp)

end PercLib.Percolation.Bond
