/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Generation cardinalities of the true cluster and finite-horizon convergence.

Accepted from independent submission `smwpalb9h` direction D2.
No generation-moment induction or cluster-moment finiteness is asserted here.
-/
module

/-
Private swarm module (member m2, swarm smwpalb9h), direction 2.

Cardinality of the actual cluster as `1 + Σ_k |G (k+1)|`, in `ℕ∞` (supremum of
finite partial sums) and in `ℝ≥0∞` (genuine `tsum`), together with monotone
finite-horizon convergence.  No finite-window hypothesis: the identity is for
the true cluster `cluster ω o`.
-/
public import PercLib.CriticalLRP.Exploration.BFS.Measurable
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false


@[expose] public section

noncomputable section

open MeasureTheory Set Filter PercLib.Percolation.Bond
open scoped ENNReal BigOperators Topology

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

/-! ### The finite horizon and its cardinality -/

theorem horizon_eq_P_succ (ω : Config V) (o : V) (k : ℕ) :
    horizon ω o k = P ω o (k + 1) := by
  rw [horizon_eq, P_succ]

theorem horizon_succ (ω : Config V) (o : V) (k : ℕ) :
    horizon ω o (k + 1) = horizon ω o k ∪ gen ω o k := by
  rw [horizon_eq_P_succ, horizon_eq_P_succ, P_succ, gen]

theorem disjoint_horizon_gen (ω : Config V) (o : V) (k : ℕ) :
    Disjoint (horizon ω o k) (gen ω o k) := by
  rw [horizon_eq_P_succ, gen]
  exact disjoint_P_A ω o (k + 1)

theorem horizon_mono (ω : Config V) (o : V) : Monotone (horizon ω o) := by
  intro i j h
  induction h with
  | refl => exact subset_rfl
  | step _ ih =>
      exact ih.trans (by rw [horizon_succ]; exact Set.subset_union_left)

theorem horizon_subset_cluster (ω : Config V) (o : V) (k : ℕ) :
    horizon ω o k ⊆ cluster ω o := by
  intro y hy
  rw [horizon_eq] at hy
  rcases hy with hyP | hyA
  · rw [P_eq_iUnion] at hyP
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hyP
    exact A_subset_cluster ω o j hj
  · exact A_subset_cluster ω o k hyA

theorem A_subset_horizon_succ (ω : Config V) (o : V) (k : ℕ) :
    A ω o k ⊆ horizon ω o (k + 1) := by
  rw [horizon_eq_P_succ]
  exact (A_subset_P_succ ω o k).trans (P_subset_succ ω o (k + 1))

/-- The cluster is the increasing union of the finite horizons. -/
theorem cluster_eq_iUnion_horizon (ω : Config V) (o : V) :
    cluster ω o = ⋃ k, horizon ω o k := by
  rw [cluster_eq_iUnion_A]
  apply le_antisymm
  · intro y hy
    rw [Set.mem_iUnion] at hy ⊢
    obtain ⟨k, hk⟩ := hy
    exact ⟨k + 1, A_subset_horizon_succ ω o k hk⟩
  · intro y hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨k, hk⟩ := hy
    have hcl : y ∈ cluster ω o := horizon_subset_cluster ω o k hk
    rwa [cluster_eq_iUnion_A] at hcl

theorem encard_horizon (ω : Config V) (o : V) (k : ℕ) :
    (horizon ω o k).encard = 1 + ∑ j ∈ Finset.range k, (gen ω o j).encard := by
  induction k with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      rw [horizon_eq, P_zero, A_zero, Set.empty_union, Set.encard_singleton, add_zero]
  | succ k ih =>
      rw [horizon_succ, Set.encard_union_eq (disjoint_horizon_gen ω o k), ih,
        Finset.sum_range_succ, add_assoc]

/-! ### A monotone union of sets has cardinality the supremum of cardinalities -/

theorem exists_eq_of_monotone_of_finite {α : Type*} {s : ℕ → Set α} (hmono : Monotone s)
    (hfin : (⋃ n, s n).Finite) : ∃ N, ⋃ n, s n = s N := by
  obtain ⟨I, hIfin, hI⟩ := Set.finite_subset_iUnion hfin (subset_rfl :
    (⋃ n, s n) ⊆ ⋃ n, s n)
  obtain ⟨N, hN⟩ := hIfin.bddAbove
  refine ⟨N, le_antisymm ?_ (Set.subset_iUnion s N)⟩
  intro x hx
  have hx' := hI hx
  rw [Set.mem_iUnion] at hx'
  obtain ⟨i, hx'⟩ := hx'
  rw [Set.mem_iUnion] at hx'
  obtain ⟨hiI, hix⟩ := hx'
  exact hmono (hN hiI) hix

theorem encard_iUnion_nat_eq_iSup {α : Type*} {s : ℕ → Set α} (hmono : Monotone s) :
    (⋃ n, s n).encard = ⨆ n, (s n).encard := by
  apply le_antisymm
  · by_cases hfin : (⋃ n, s n).Finite
    · obtain ⟨N, hN⟩ := exists_eq_of_monotone_of_finite hmono hfin
      rw [hN]
      exact le_iSup (fun n => (s n).encard) N
    · rw [Set.Infinite.encard_eq hfin]
      by_contra hne
      have hlt : (⨆ n, (s n).encard) < ⊤ := not_le.mp hne
      obtain ⟨N, hN⟩ := ENat.exists_eq_iSup_of_lt_top hlt
      have hfinN : (s N).Finite := Set.encard_lt_top_iff.mp (hN ▸ hlt)
      have hstable : ∀ n ≥ N, s n = s N := by
        intro n hn
        have hle : (s n).encard ≤ (s N).encard := by
          calc (s n).encard ≤ ⨆ m, (s m).encard := le_iSup (fun m => (s m).encard) n
            _ = (s N).encard := hN.symm
        exact (Set.Finite.eq_of_subset_of_encard_le (s := s N) (t := s n) hfinN
          (hmono hn) hle).symm
      have hunion : ⋃ n, s n = s N := by
        apply le_antisymm
        · intro x hx
          rw [Set.mem_iUnion] at hx
          obtain ⟨n, hn⟩ := hx
          rcases Nat.lt_or_ge n N with h | h
          · exact hmono h.le hn
          · rw [← hstable n h]
            exact hn
        · exact Set.subset_iUnion s N
      exact hfin (hunion ▸ hfinN)
  · exact iSup_le fun n => Set.encard_mono (Set.subset_iUnion s n)

/-! ### The counting identities -/

/-- The cardinality of the actual cluster is one plus the supremum of the finite
partial sums of generation cardinalities (the `ℕ∞`-sum). -/
theorem encard_cluster_eq_iSup_horizon (ω : Config V) (o : V) :
    (cluster ω o).encard = ⨆ k, (horizon ω o k).encard := by
  rw [cluster_eq_iUnion_horizon, encard_iUnion_nat_eq_iSup (horizon_mono ω o)]


theorem encard_cluster_eq_iSup (ω : Config V) (o : V) :
    (cluster ω o).encard =
      ⨆ k, (1 + ∑ j ∈ Finset.range k, (gen ω o j).encard) := by
  rw [encard_cluster_eq_iSup_horizon]
  exact iSup_congr fun k => encard_horizon ω o k

/-- The coercion `ℕ∞ → ℝ≥0∞` commutes with countable suprema. -/
theorem toENNReal_iSup_nat (f : ℕ → ℕ∞) :
    ((⨆ n, f n : ℕ∞) : ℝ≥0∞) = ⨆ n, (f n : ℝ≥0∞) := by
  rcases eq_or_ne (⨆ n, f n) ⊤ with h | h
  · rw [h, ENat.toENNReal_top]
    symm
    apply le_antisymm le_top
    rw [top_le_iff, iSup_eq_top]
    intro b hb
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hb.ne
    have hklt : (k : ℕ∞) < ⊤ := by simp
    obtain ⟨n, hn⟩ := (iSup_eq_top.mp h) (k : ℕ∞) hklt
    exact ⟨n, lt_of_lt_of_le hk (ENat.toENNReal_le.mpr hn.le)⟩
  · have hlt : (⨆ n, f n) < ⊤ := lt_top_iff_ne_top.mpr h
    obtain ⟨N, hN⟩ := ENat.exists_eq_iSup_of_lt_top hlt
    have hsup : ∀ n, f n ≤ f N := by
      intro n
      rw [hN]
      exact le_iSup (fun n => f n) n
    have hval : (⨆ n, (f n : ℝ≥0∞)) = (f N : ℝ≥0∞) := by
      apply le_antisymm
      · exact iSup_le fun n => ENat.toENNReal_le.mpr (hsup n)
      · exact le_iSup (fun n => (f n : ℝ≥0∞)) N
    rw [← hN, hval]

/-- The cardinality of the actual cluster is one plus the genuine `tsum` of the
generation cardinalities in `ℝ≥0∞`. -/
theorem encard_cluster_toENNReal_eq_tsum (ω : Config V) (o : V) :
    ((cluster ω o).encard : ℝ≥0∞) =
      1 + ∑' j : ℕ, ((gen ω o j).encard : ℝ≥0∞) := by
  rw [encard_cluster_eq_iSup, toENNReal_iSup_nat, ENNReal.tsum_eq_iSup_nat,
    ENNReal.add_iSup]
  apply iSup_congr
  intro k
  rw [ENat.toENNReal_add, ENat.toENNReal_one,
    show ((∑ j ∈ Finset.range k, (gen ω o j).encard : ℕ∞) : ℝ≥0∞)
      = ∑ j ∈ Finset.range k, ((gen ω o j).encard : ℝ≥0∞) from
      map_sum ENat.toENNRealRingHom _ _]

/-- Monotone finite-horizon convergence of the cluster cardinality in `ℝ≥0∞`. -/
theorem tendsto_encard_horizon (ω : Config V) (o : V) :
    Tendsto (fun k => ((horizon ω o k).encard : ℝ≥0∞)) atTop
      (𝓝 ((cluster ω o).encard : ℝ≥0∞)) := by
  have hmono : Monotone fun k => ((horizon ω o k).encard : ℝ≥0∞) :=
    fun i j h => ENat.toENNReal_le.mpr (Set.encard_mono (horizon_mono ω o h))
  have h := tendsto_atTop_iSup hmono
  rwa [← toENNReal_iSup_nat, ← encard_cluster_eq_iSup_horizon] at h

end PercLib.CriticalLRP.Exploration.BFS
