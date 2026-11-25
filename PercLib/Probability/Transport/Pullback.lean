/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 197 (Q-37), written on 2026-11-15 by PROVER-E. No upstream proof is
copied.
-/
module

public import Mathlib.Probability.ProductMeasure
public import PercLib.Probability.ProdBernoulli

/-!
# Pulling configurations back along an injective map of indices

For an injective `g : J → I`, the map `ω ↦ g ⁻¹' ω` sends `prodBernoulli p` to
`prodBernoulli (p ∘ g)` (`prodBernoulli_map_preimage`). For an equivalence this is the
reindexing of `PercLib.Probability.Transport.Reindexing`; injectivity alone suffices. This
file adds no definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace PercLib.Probability

variable {I J : Type*}

/-- Product measures pull back along injective maps of indices. -/
theorem infinitePi_map_comp_injective {X : Type*} [MeasurableSpace X] (μ : I → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] {g : J → I} (hg : Function.Injective g) :
    (Measure.infinitePi μ).map (fun P : I → X => fun j => P (g j)) =
      Measure.infinitePi fun j => μ (g j) := by
  classical
  have hm : Measurable fun P : I → X => fun j => P (g j) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply (g j)
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  set t' : I → Set X := fun i => if h : ∃ j ∈ s, g j = i then t h.choose else univ
  have ht' : ∀ j ∈ s, t' (g j) = t j := by
    intro j hj
    have hex : ∃ j' ∈ s, g j' = g j := ⟨j, hj, rfl⟩
    simp only [t', hex, ↓reduceDIte]
    rw [hg hex.choose_spec.2]
  have hpre : (fun P : I → X => fun j => P (g j)) ⁻¹' (s : Set J).pi t =
      ((s.map ⟨g, hg⟩ : Finset I) : Set I).pi t' := by
    ext P
    simp only [mem_preimage, mem_pi, Finset.mem_coe, Finset.mem_map,
      Function.Embedding.coeFn_mk, forall_exists_index, and_imp]
    constructor
    · rintro h _ j hj rfl
      rw [ht' j hj]
      exact h j hj
    · intro h j hj
      rw [← ht' j hj]
      exact h _ j hj rfl
  rw [hpre, Measure.infinitePi_pi]
  · rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun j hj => by
      simp only [Function.Embedding.coeFn_mk, ht' j hj]
  · intro i _
    simp only [t']
    split_ifs with h
    · exact ht _
    · exact MeasurableSet.univ

/-- **Pullback of configurations along an injective map of indices.** -/
theorem prodBernoulli_map_preimage (p : I → unitInterval) {g : J → I}
    (hg : Function.Injective g) :
    (prodBernoulli p).map (fun ω : Set I => g ⁻¹' ω) = prodBernoulli (p ∘ g) := by
  have hset : Measurable fun P : I → Prop => {i | P i} := MeasurableEquiv.setOfPred.measurable
  have hsetJ : Measurable fun P : J → Prop => {j | P j} := MeasurableEquiv.setOfPred.measurable
  have hpre : Measurable fun ω : Set I => g ⁻¹' ω :=
    Measurable.of_mem fun j => (measurableSet_mem (g j)).mem
  have hcomp : Measurable fun P : I → Prop => fun j => P (g j) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply (g j)
  rw [prodBernoulli_eq_map, prodBernoulli_eq_map, Measure.map_map hpre hset,
    show ((fun ω : Set I => g ⁻¹' ω) ∘ fun P : I → Prop => {i | P i}) =
      (fun P : J → Prop => {j | P j}) ∘ fun P : I → Prop => fun j => P (g j) from rfl,
    ← Measure.map_map hsetJ hcomp, infinitePi_map_comp_injective _ hg]
  rfl

/-- The pullback of a measurable event along an injective map of indices. -/
theorem prodBernoulli_preimage_preimage (p : I → unitInterval) {g : J → I}
    (hg : Function.Injective g) {A : Set (Set J)} (hA : MeasurableSet A) :
    prodBernoulli p {ω | g ⁻¹' ω ∈ A} = prodBernoulli (p ∘ g) A := by
  have hpre : Measurable fun ω : Set I => g ⁻¹' ω :=
    Measurable.of_mem fun j => (measurableSet_mem (g j)).mem
  rw [← prodBernoulli_map_preimage p hg, Measure.map_apply hpre hA]
  rfl

/-! ### Non-vacuity -/

/-- The even coordinates of `ℕ` under a constant profile. -/
example (p : unitInterval) :
    prodBernoulli (fun _ : ℕ => p) {ω | (fun n => 2 * n) ⁻¹' ω ∈ {ω : Set ℕ | 0 ∈ ω}} =
      prodBernoulli (fun _ : ℕ => p) {ω : Set ℕ | 0 ∈ ω} :=
  prodBernoulli_preimage_preimage _ (fun a b h => by simpa using h) (measurableSet_mem 0)

end PercLib.Probability
