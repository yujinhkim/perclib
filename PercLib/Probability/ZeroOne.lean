/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 118 (Q-2), written on 2026-11-14 by PROVER-E. No upstream proof is
copied: the result is mathlib's Kolmogorov zero-one law
`ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup` applied to the coordinate
independence `PercLib.Probability.prodBernoulli_iIndepFun_mem`.
-/
module

public import Mathlib.Probability.Independence.ZeroOne
public import PercLib.Probability.ProdBernoulliIndependence

/-!
# The zero-one law for events invariant under finite modification

An event `A ⊆ Set ι` that does not change when one index is added,
`insert i ω ∈ A ↔ ω ∈ A`, also does not change when one index is removed, hence is
unchanged by every finite modification. It is then a tail event of the coordinate
σ-algebras, and Kolmogorov's zero-one law gives `prodBernoulli p A ∈ {0, 1}`.

No countability of `ι` is needed: the tail σ-algebra is taken along the cofinite filter,
with the directed family of finite sets of indices. This file adds no definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter

namespace PercLib.Probability

variable {ι : Type*}

/-- An event invariant under adding one index is invariant under removing one. -/
theorem diff_singleton_mem_iff_of_insert_iff {A : Set (Set ι)}
    (hflip : ∀ ω i, insert i ω ∈ A ↔ ω ∈ A) (ω : Set ι) (i : ι) :
    ω \ {i} ∈ A ↔ ω ∈ A := by
  rw [← hflip, insert_sdiff_singleton, hflip]

/-- An event invariant under adding one index is invariant under removing a finite set. -/
theorem diff_finset_mem_iff_of_insert_iff {A : Set (Set ι)}
    (hflip : ∀ ω i, insert i ω ∈ A ↔ ω ∈ A) (ω : Set ι) (F : Finset ι) :
    ω \ (F : Set ι) ∈ A ↔ ω ∈ A := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert i F _ ih =>
    rw [Finset.coe_insert, insert_eq, union_comm, ← sdiff_sdiff,
      diff_singleton_mem_iff_of_insert_iff hflip, ih]

/-- An event invariant under adding one index is measurable for the tail σ-algebra of the
coordinates, taken along the cofinite filter. -/
theorem measurableSet_limsup_cofinite_of_insert_iff {A : Set (Set ι)} (hA : MeasurableSet A)
    (hflip : ∀ ω i, insert i ω ∈ A ↔ ω ∈ A) :
    MeasurableSet[limsup (fun i : ι => MeasurableSpace.comap (fun ω : Set ι => i ∈ ω) ⊤)
      cofinite] A := by
  rw [limsup_eq, MeasurableSpace.measurableSet_sInf]
  intro m hm
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∀ i ∉ F,
      MeasurableSpace.comap (fun ω : Set ι => i ∈ ω) ⊤ ≤ m := by
    have hfin := Filter.eventually_cofinite.1 hm
    refine ⟨hfin.toFinset, fun i hi => ?_⟩
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have hg : @Measurable (Set ι) (Set ι) m Set.instMeasurableSpace
      (fun ω : Set ι => ω \ (F : Set ι)) := by
    refine Measurable.of_mem (fun i : ι => ?_)
    by_cases hi : i ∈ F
    · have : (fun ω : Set ι => i ∈ ω \ (F : Set ι)) = fun _ => False := by
        funext ω; simp [hi]
      rw [this]
      exact measurable_const
    · have : (fun ω : Set ι => i ∈ ω \ (F : Set ι)) = fun ω => i ∈ ω := by
        funext ω; simp [hi]
      rw [this]
      exact (comap_measurable (fun ω : Set ι => i ∈ ω)).mono (hF i hi) le_rfl
  have hpre : (fun ω : Set ι => ω \ (F : Set ι)) ⁻¹' A = A := by
    ext ω
    exact diff_finset_mem_iff_of_insert_iff hflip ω F
  rw [← hpre]
  exact hg hA

/-- **Zero-one law for events invariant under finite modification.** If adding one index
never changes membership of a measurable event, its probability is `0` or `1`, for every
profile and every index type. -/
theorem prodBernoulli_eq_zero_or_one_of_insert_iff (p : ι → unitInterval)
    {A : Set (Set ι)} (hA : MeasurableSet A) (hflip : ∀ ω i, insert i ω ∈ A ↔ ω ∈ A) :
    prodBernoulli p A = 0 ∨ prodBernoulli p A = 1 := by
  classical
  have hind : iIndep (fun i : ι => MeasurableSpace.comap (fun ω : Set ι => i ∈ ω) ⊤)
      (prodBernoulli p) :=
    (iIndepFun_iff_iIndep _ _ _).1 (prodBernoulli_iIndepFun_mem p)
  exact measure_zero_or_one_of_measurableSet_limsup
    (fun i => (measurable_set_mem i).comap_le) hind
    (p := fun t : Set ι => t.Finite) (ns := fun F : Finset ι => (F : Set ι))
    (fun t ht => ht.compl_mem_cofinite)
    (fun F G => ⟨F ∪ G, by simp, by simp⟩)
    (fun F => F.finite_toSet)
    (fun i => ⟨{i}, by simp⟩)
    (measurableSet_limsup_cofinite_of_insert_iff hA hflip)

/-! Non-vacuity: on a finite index type the hypothesis forces the empty or the full event,
and both probabilities occur for a nontrivial tail event on `ℕ`. -/

example (p : Bool → unitInterval) :
    prodBernoulli p (∅ : Set (Set Bool)) = 0 ∨ prodBernoulli p (∅ : Set (Set Bool)) = 1 :=
  prodBernoulli_eq_zero_or_one_of_insert_iff p MeasurableSet.empty (by simp)

/-- The event "infinitely many indices are open" is invariant under finite modification. -/
example (p : ℕ → unitInterval) :
    prodBernoulli p {ω : Set ℕ | ω.Infinite} = 0 ∨
      prodBernoulli p {ω : Set ℕ | ω.Infinite} = 1 := by
  refine prodBernoulli_eq_zero_or_one_of_insert_iff p ?_ fun ω i => not_congr finite_insert
  have : {ω : Set ℕ | ω.Infinite} = ⋂ n : ℕ, ⋃ m : ℕ, ⋃ (_ : n ≤ m), {ω | m ∈ ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
    exact Nat.frequently_atTop_iff_infinite.symm.trans (Filter.frequently_atTop)
  rw [this]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
    MeasurableSet.iUnion fun _ => measurableSet_mem m

end PercLib.Probability
