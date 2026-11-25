/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 122 (Q-6), written on 2026-11-14 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.Algebra.Order.Floor.Extended
public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Probability.OpenEventHarris

/-!
# Finite-volume approximation of the susceptibility and of percolation

Let `S : ℕ → Set V` be an exhaustion: monotone, with every vertex in some `S n`. The
internal cluster of `x` in `S n` is written out explicitly (no new definition):
`{y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n, ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩}`.

* `iUnion_induce_cluster`: the internal clusters increase to the cluster;
* `encard_cluster_eq_iSup_induce`: the volume is the supremum of internal volumes;
* `chi_eq_iSup_lintegral_induce`: the susceptibility is the supremum of internal
  expected volumes (monotone convergence; infinite values allowed);
* `escape_eq_iSup_induce`: escape probabilities are suprema of internal escape
  probabilities;
* `law_cluster_infinite_eq_iInf_escape`: `θ(x)` is the infimum of the probabilities of
  escaping an increasing exhaustion by finite sets;
* `law_cluster_infinite_eq_iInf_iSup_induce`: the combination of the last two.

This file adds no definition.
-/

@[expose] public section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The cardinality of an increasing union is the supremum of the cardinalities. -/
theorem encard_iUnion_of_monotone {α : Type*} {K : ℕ → Set α} (hK : Monotone K) :
    (⋃ n, K n).encard = ⨆ n, (K n).encard := by
  refine le_antisymm ?_ (iSup_le fun n => encard_le_encard (subset_iUnion K n))
  refine ENat.forall_natCast_le_iff_le.1 fun a ha => ?_
  obtain ⟨t, htU, hta⟩ := exists_subset_encard_eq ha
  have htfin : t.Finite := finite_of_encard_eq_coe hta
  obtain ⟨n, hn⟩ := hK.directed_le.exists_mem_subset_of_finset_subset_biUnion
    (s := htfin.toFinset) (by rwa [Finite.coe_toFinset])
  rw [Finite.coe_toFinset] at hn
  rw [← hta]
  exact (encard_le_encard hn).trans (le_iSup (fun n => (K n).encard) n)

/-- Internal clusters increase with the domain. -/
theorem monotone_induce_cluster {S : ℕ → Set V} (hS : Monotone S) (ω : Config V) (x : V) :
    Monotone fun n => {y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
      ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩} :=
  fun _ _ hnm _ hy => monotone_localConn hS x _ hnm hy

/-- **The internal clusters increase to the cluster.** -/
theorem iUnion_induce_cluster {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n)
    (ω : Config V) (x : V) :
    (⋃ n, {y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
      ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩}) = cluster ω x := by
  ext y
  rw [mem_cluster_iff, conn_eq_iUnion_localConn hS hcover]
  simp only [mem_iUnion, mem_ofPred_eq]

/-- **The cluster volume is the supremum of the internal volumes.** -/
theorem encard_cluster_eq_iSup_induce {S : ℕ → Set V} (hS : Monotone S)
    (hcover : ∀ v, ∃ n, v ∈ S n) (ω : Config V) (x : V) :
    (cluster ω x).encard = ⨆ n, ({y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
      ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩} : Set V).encard := by
  rw [← iUnion_induce_cluster hS hcover ω x,
    encard_iUnion_of_monotone (monotone_induce_cluster hS ω x)]

/-- An internal connection event is measurable when there are countably many vertices. -/
theorem measurableSet_induce_conn [Countable V] (S : Set V) (x y : V) :
    MeasurableSet {ω : Config V | ∃ hx : x ∈ S, ∃ hy : y ∈ S,
      ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩} := by
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · have : {ω : Config V | ∃ hx : x ∈ S, ∃ hy : y ∈ S,
          ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩} =
          {ω : Config V | ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩} := by
        ext ω
        simp only [mem_ofPred_eq]
        exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hx, hy, h⟩⟩
      rw [this]
      exact measurableSet_localConn S ⟨x, hx⟩ ⟨y, hy⟩
    · have : {ω : Config V | ∃ hx : x ∈ S, ∃ hy : y ∈ S,
          ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun ⟨_, h, _⟩ => hy h
      rw [this]
      exact MeasurableSet.empty
  · have : {ω : Config V | ∃ hx : x ∈ S, ∃ hy : y ∈ S,
        ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun ⟨h, _, _⟩ => hx h
    rw [this]
    exact MeasurableSet.empty

/-- The internal cluster volume is measurable when there are countably many vertices. -/
theorem measurable_encard_induce_cluster [Countable V] (S : Set V) (x : V) :
    Measurable fun ω : Config V => ({y | ∃ hx : x ∈ S, ∃ hy : y ∈ S,
      ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩} : Set V).encard := by
  refine measurable_encard.comp (Measurable.of_mem fun y => ?_)
  exact (measurableSet_induce_conn S x y).mem

/-- **The susceptibility is the supremum of the internal expected volumes.** Infinite
values are allowed on both sides. -/
theorem chi_eq_iSup_lintegral_induce [Countable V] (q : Sym2 V → unitInterval)
    {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n) (x : V) :
    chi q x = ⨆ n, ∫⁻ ω, (({y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
      ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩} : Set V).encard : ℝ≥0∞)
        ∂law q := by
  rw [chi]
  simp_rw [encard_cluster_eq_iSup_induce hS hcover _ x, ENat.toENNReal_iSup]
  refine lintegral_iSup (fun n => ?_) (fun n m hnm ω => ?_)
  · exact (measurable_of_countable _).comp (measurable_encard_induce_cluster (S n) x)
  · exact ENat.toENNReal_le.2 (encard_le_encard (monotone_induce_cluster hS ω x hnm))

/-- **Escape probabilities are suprema of internal escape probabilities.** -/
theorem escape_eq_iSup_induce (q : Sym2 V → unitInterval) {S : ℕ → Set V} (hS : Monotone S)
    (hcover : ∀ v, ∃ n, v ∈ S n) (x : V) (F : Set V) :
    law q (⋃ y ∈ Fᶜ, conn x y) = ⨆ n, law q {ω | ∃ y ∉ F, y ∈ {y | ∃ hx : x ∈ S n,
      ∃ hy : y ∈ S n, ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩}} := by
  have hmono : Monotone fun n => {ω : Config V | ∃ y ∉ F, y ∈ {y | ∃ hx : x ∈ S n,
      ∃ hy : y ∈ S n, ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩}} :=
    fun n m hnm ω ⟨y, hyF, hy⟩ => ⟨y, hyF, monotone_induce_cluster hS ω x hnm hy⟩
  rw [← hmono.measure_iUnion]
  congr 1
  ext ω
  simp only [mem_iUnion, mem_ofPred_eq, mem_compl_iff, exists_prop]
  constructor
  · rintro ⟨y, hyF, hxy⟩
    have : y ∈ cluster ω x := hxy
    rw [← iUnion_induce_cluster hS hcover ω x, mem_iUnion] at this
    obtain ⟨n, hn⟩ := this
    exact ⟨n, y, hyF, hn⟩
  · rintro ⟨n, y, hyF, hn⟩
    refine ⟨y, hyF, ?_⟩
    have : y ∈ cluster ω x := by
      rw [← iUnion_induce_cluster hS hcover ω x, mem_iUnion]
      exact ⟨n, hn⟩
    exact this

/-- The infinite-cluster event is the decreasing intersection of escapes from the sets
of an exhaustion by finite sets. -/
theorem cluster_infinite_eq_iInter_escape {F : ℕ → Set V} (hF : Monotone F)
    (hfin : ∀ m, (F m).Finite) (hcov : ∀ v, ∃ m, v ∈ F m) (x : V) :
    {ω : Config V | (cluster ω x).Infinite} = ⋂ m, ⋃ y ∈ (F m)ᶜ, conn x y := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_compl_iff, exists_prop]
  constructor
  · intro hinf m
    obtain ⟨y, hy, hyF⟩ := (hinf.sdiff (hfin m)).nonempty
    exact ⟨y, hyF, hy⟩
  · intro h hK
    have hsub : ((hK.toFinset : Finset V) : Set V) ⊆ ⋃ m, F m := by
      intro v _
      exact mem_iUnion.2 (hcov v)
    obtain ⟨m, hm⟩ := hF.directed_le.exists_mem_subset_of_finset_subset_biUnion hsub
    obtain ⟨y, hyF, hy⟩ := h m
    have hy' : y ∈ cluster ω x := hy
    exact hyF (hm (by simpa using hy'))

/-- **`θ(x)` is the infimum of escape probabilities from an exhaustion by finite sets.** -/
theorem law_cluster_infinite_eq_iInf_escape [Countable V] (q : Sym2 V → unitInterval)
    {F : ℕ → Set V} (hF : Monotone F) (hfin : ∀ m, (F m).Finite) (hcov : ∀ v, ∃ m, v ∈ F m)
    (x : V) :
    law q {ω | (cluster ω x).Infinite} = ⨅ m, law q (⋃ y ∈ (F m)ᶜ, conn x y) := by
  rw [cluster_infinite_eq_iInter_escape hF hfin hcov x]
  have hanti : Antitone fun m => (⋃ y ∈ (F m)ᶜ, conn x y : Set (Config V)) :=
    fun m m' hmm' => biUnion_subset_biUnion_left (compl_subset_compl.2 (hF hmm'))
  exact hanti.measure_iInter (fun m => (measurableSet_escape x (F m)).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩

/-- **`θ(x)` through internal clusters.** -/
theorem law_cluster_infinite_eq_iInf_iSup_induce [Countable V] (q : Sym2 V → unitInterval)
    {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n)
    {F : ℕ → Set V} (hF : Monotone F) (hfin : ∀ m, (F m).Finite) (hcov : ∀ v, ∃ m, v ∈ F m)
    (x : V) :
    law q {ω | (cluster ω x).Infinite} = ⨅ m, ⨆ n, law q {ω | ∃ y ∉ F m,
      y ∈ {y | ∃ hx : x ∈ S n, ∃ hy : y ∈ S n,
        ((openGraph ω).induce (S n)).Reachable ⟨x, hx⟩ ⟨y, hy⟩}} := by
  rw [law_cluster_infinite_eq_iInf_escape q hF hfin hcov x]
  simp_rw [escape_eq_iSup_induce q hS hcover x]

/-! ### Non-vacuity -/

/-- With `S n = univ` the internal cluster is the cluster. -/
example (ω : Config V) (x : V) :
    (⋃ _n : ℕ, {y | ∃ hx : x ∈ (univ : Set V), ∃ hy : y ∈ (univ : Set V),
      ((openGraph ω).induce (univ : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩}) = cluster ω x :=
  iUnion_induce_cluster (S := fun _ => univ) (fun _ _ _ => le_rfl) (fun _ => ⟨0, trivial⟩) ω x

/-- On `ℕ`, with the initial segments as exhaustion, both for the domains (whose first
term misses the root `5`) and for the finite sets. -/
example (q : Sym2 ℕ → unitInterval) :
    law q {ω | (cluster ω 5).Infinite} = ⨅ m, ⨆ n, law q {ω | ∃ y ∉ Iic m,
      y ∈ {y | ∃ hx : 5 ∈ Iic n, ∃ hy : y ∈ Iic n,
        ((openGraph ω).induce (Iic n)).Reachable ⟨5, hx⟩ ⟨y, hy⟩}} :=
  law_cluster_infinite_eq_iInf_iSup_induce q (fun _ _ h => Iic_subset_Iic.2 h)
    (fun v => ⟨v, mem_Iic.2 le_rfl⟩) (fun _ _ h => Iic_subset_Iic.2 h) (fun m => finite_Iic m)
    (fun v => ⟨v, mem_Iic.2 le_rfl⟩) 5

end PercLib.Percolation.Bond
